// Moduflux - module "Auto Totem" for LeviLauncher / preloader-android.
// Target: Minecraft Bedrock 1.26.52.3 (arm64-v8a), worlds HOSTED on this phone.
//
// What it does: when the totem in your offhand is used up (pops), it immediately moves
// another totem from your inventory into the offhand. If you have no other totem, it
// does nothing.
//
// How it knows what a "totem" is: it remembers the item type that is in your offhand when
// you switch Auto Totem on (or when you press the LT button). So: hold a totem in your
// offhand, then switch Auto Totem on.
//
// Everything is found by exact byte signatures, so on a different Minecraft version the
// mod simply refuses to start (no crash).

#include <android/log.h>

#include <atomic>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <string>
#include <string_view>
#include <unordered_map>

#include <pl/Mod.hpp>
#include <pl/ModMenu.hpp>
#include <pl/memory/Hook.hpp>
#include <pl/memory/Signature.hpp>
#include <pl/memory/Vtable.hpp>

namespace {

constexpr const char *kTag = "Moduflux";
constexpr const char *kGameLib = "libminecraftpe.so";

void logi(const char *fmt, const void *a = nullptr, const void *b = nullptr) {
  __android_log_print(ANDROID_LOG_INFO, kTag, fmt, a, b);
}

// ---- Menu ids --------------------------------------------------------------
constexpr const char *kModule = "moduflux.autototem";
constexpr const char *kLearnButton = "moduflux.autototem.learn";

// ---- Where things are in Minecraft 1.26.52.3 --------------------------------
// GameMode::tick (called every game tick for every player's game mode).
constexpr const char *kTickSignature =
    "FD 7B BE A9 F3 0B 00 F9 FD 03 00 91 F3 03 00 AA 00 5C 40 F9 08 00 40 F9 "
    "08 11 40 F9 00 01 3F D6 60 26 40 BD 60 22 00 BD";
// Actor::getOffhandSlot() const  -> ItemStack const&   (the bl at +12 calls the
// "hand container" helper, which we also reuse to be able to write the offhand).
constexpr const char *kOffhandSignature =
    "FD 7B BF A9 FD 03 00 91 00 20 00 91 ?? ?? ?? ?? 08 00 40 F9 02 21 40 F9 "
    "21 00 80 52 FD 7B C1 A8 40 00 1F D6 28 1C 00 72";

constexpr size_t kPlayerInventoryOffset = 0x570; // Player -> PlayerInventory*
constexpr size_t kInventoryOffset = 0xB8;        // PlayerInventory -> Inventory*
constexpr size_t kGameModePlayerOffset = 0x8;    // GameMode -> Player*
constexpr size_t kActorPosOffset = 0x208;        // Actor -> Vec3* (x, y, z floats)
constexpr size_t kEntityContextOffset = 0x8;     // Actor -> EntityContext (helper arg)

// Container virtual slots (same for the inventory and the hand container).
constexpr size_t kSlotGetItem = 8;
constexpr size_t kSlotSetItem = 13;
constexpr size_t kSlotRemoveItem = 15;
constexpr size_t kSlotGetSize = 21;

// ItemStack layout (size 0x98).
constexpr size_t kStackItemOffset = 0x08;  // -> holder -> Item*
constexpr size_t kStackCountOffset = 0x22; // uint8
constexpr size_t kStackValidOffset = 0x23; // bool

// ---- Function pointers (filled in by installAll) ----------------------------
using TickFn = void (*)(void *gameMode);
using OffhandFn = const uint8_t *(*)(void *actor);
using HandContainerFn = void *(*)(void *entityContext);

TickFn orig_tick = nullptr;
void *g_tickTarget = nullptr;
OffhandFn g_getOffhand = nullptr;
HandContainerFn g_getHandContainer = nullptr;
uintptr_t g_serverFn0 = 0; // slot 0 of ServerPlayer's vtable (to recognise a ServerPlayer)
uintptr_t g_localFn0 = 0;  // slot 0 of LocalPlayer's vtable

// ---- State ------------------------------------------------------------------
std::atomic<bool> g_enabled{false};
std::atomic<bool> g_learnRequested{false};
std::atomic<void *> g_learnedItem{nullptr};
std::atomic<bool> g_installed{false};

// Position of the local (own) player, so we only act for the host's player and not for
// friends who joined the hosted world.
std::atomic<bool> g_haveLocal{false};
std::atomic<float> g_localX{0}, g_localY{0}, g_localZ{0};

struct PlayerState {
  bool hadTotem = false;
};
std::unordered_map<void *, PlayerState> g_players; // only touched on the server thread

// ---- Small helpers for talking to game objects --------------------------------
inline void **vtableOf(void *obj) { return *reinterpret_cast<void ***>(obj); }

inline const uint8_t *containerGetItem(void *c, int slot) {
  using Fn = const uint8_t *(*)(void *, int);
  return reinterpret_cast<Fn>(vtableOf(c)[kSlotGetItem])(c, slot);
}
inline void containerSetItem(void *c, int slot, const uint8_t *stack) {
  using Fn = void (*)(void *, int, const uint8_t *);
  reinterpret_cast<Fn>(vtableOf(c)[kSlotSetItem])(c, slot, stack);
}
inline void containerRemoveItem(void *c, int slot, int count) {
  using Fn = void (*)(void *, int, int);
  reinterpret_cast<Fn>(vtableOf(c)[kSlotRemoveItem])(c, slot, count);
}
inline int containerSize(void *c) {
  using Fn = int (*)(void *);
  return reinterpret_cast<Fn>(vtableOf(c)[kSlotGetSize])(c);
}

// True if `stack` holds at least one item; `itemOut` receives the item type pointer.
bool stackHasItem(const uint8_t *stack, void **itemOut = nullptr) {
  if (!stack) return false;
  if (stack[kStackValidOffset] == 0) return false;
  if (stack[kStackCountOffset] == 0) return false;
  void *holder = *reinterpret_cast<void *const *>(stack + kStackItemOffset);
  if (!holder) return false;
  void *item = *reinterpret_cast<void *const *>(holder);
  if (!item) return false;
  if (itemOut) *itemOut = item;
  return true;
}

inline void *getPtr(void *base, size_t offset) {
  return *reinterpret_cast<void **>(reinterpret_cast<uint8_t *>(base) + offset);
}

bool actorPosition(void *actor, float &x, float &y, float &z) {
  const float *p = reinterpret_cast<const float *>(getPtr(actor, kActorPosOffset));
  if (!p) return false;
  x = p[0];
  y = p[1];
  z = p[2];
  return true;
}

// Moves the first matching item from the inventory into the (empty) offhand.
bool refillOffhand(void *player, void *wantedItem) {
  void *playerInv = getPtr(player, kPlayerInventoryOffset);
  if (!playerInv) return false;
  void *inv = getPtr(playerInv, kInventoryOffset);
  if (!inv) return false;
  void *hand = g_getHandContainer(reinterpret_cast<uint8_t *>(player) + kEntityContextOffset);
  if (!hand) return false;

  const int size = containerSize(inv);
  if (size <= 0 || size > 128) return false;
  for (int i = 0; i < size; ++i) {
    const uint8_t *stack = containerGetItem(inv, i);
    void *item = nullptr;
    if (!stackHasItem(stack, &item) || item != wantedItem) continue;
    const int count = stack[kStackCountOffset];
    containerSetItem(hand, 1, stack);            // copy into the offhand
    containerRemoveItem(inv, i, count);          // take it out of the inventory slot
    __android_log_print(ANDROID_LOG_INFO, kTag,
                        "Auto Totem: moved item from inventory slot %d to offhand.", i);
    return true;
  }
  return false;
}

// ---- Per-tick logic ----------------------------------------------------------
void onPlayerTick(void *player) {
  void **vt = vtableOf(player);
  const uintptr_t fn0 = reinterpret_cast<uintptr_t>(vt[0]);

  if (g_localFn0 != 0 && fn0 == g_localFn0) {
    float x, y, z;
    if (actorPosition(player, x, y, z)) {
      g_localX.store(x);
      g_localY.store(y);
      g_localZ.store(z);
      g_haveLocal.store(true);
    }
    return;
  }
  if (g_serverFn0 == 0 || fn0 != g_serverFn0) return; // not a server-side player
  if (!g_enabled.load() || !g_haveLocal.load()) return;

  // Only the host's own player (the one standing where our local player is).
  float x, y, z;
  if (!actorPosition(player, x, y, z)) return;
  const float dx = x - g_localX.load(), dy = y - g_localY.load(), dz = z - g_localZ.load();
  if (dx * dx + dy * dy + dz * dz > 4.0f) return;

  const uint8_t *offhand = g_getOffhand(player);
  void *offItem = nullptr;
  bool offHas = stackHasItem(offhand, &offItem);

  if (g_learnRequested.load()) {
    g_learnRequested.store(false);
    if (offHas) {
      g_learnedItem.store(offItem);
      __android_log_print(ANDROID_LOG_INFO, kTag,
                          "Auto Totem: learned the offhand item (%p) as your totem.", offItem);
    } else {
      logi("Auto Totem: nothing in your offhand to learn. Hold a totem there and try again.");
    }
  }

  void *learned = g_learnedItem.load();
  PlayerState &st = g_players[player];
  if (learned && st.hadTotem && !offHas) {
    logi("Auto Totem: offhand totem is gone, looking for another one...");
    if (!refillOffhand(player, learned)) {
      logi("Auto Totem: no other totem in the inventory.");
    }
    // Re-read so the next tick has the right picture.
    offHas = stackHasItem(g_getOffhand(player), &offItem);
  }
  st.hadTotem = (learned && offHas && offItem == learned);
}

void hook_tick(void *gameMode) {
  orig_tick(gameMode);
  if (!g_installed.load()) return;
  void *player = getPtr(gameMode, kGameModePlayerOffset);
  if (!player) return;
  onPlayerTick(player);
}

// ---- Install / remove ---------------------------------------------------------
bool installAll() {
  if (g_installed.load()) return true;
  logi("Auto Totem: looking for game functions...");

  const uintptr_t tick = pl::memory::resolveSignature(kTickSignature, kGameLib);
  const uintptr_t offhand = pl::memory::resolveSignature(kOffhandSignature, kGameLib);
  if (tick == 0 || offhand == 0) {
    logi("Auto Totem: game functions NOT found. This Minecraft version is not supported "
         "(made for 1.26.52.3).");
    return false;
  }

  // The offhand function's 4th instruction is `bl <hand container helper>`. Decode it.
  const uint32_t blWord = *reinterpret_cast<const uint32_t *>(offhand + 12);
  if ((blWord & 0xFC000000u) != 0x94000000u) {
    logi("Auto Totem: unexpected code layout (no helper call found). Not starting.");
    return false;
  }
  int32_t imm = static_cast<int32_t>(blWord & 0x03FFFFFFu);
  if (imm & 0x02000000) imm -= 0x04000000;
  const uintptr_t helper = offhand + 12 + static_cast<intptr_t>(imm) * 4;

  g_serverFn0 = pl::memory::resolveVtableFunction("12ServerPlayer", 0, kGameLib);
  g_localFn0 = pl::memory::resolveVtableFunction("11LocalPlayer", 0, kGameLib);
  if (g_serverFn0 == 0) {
    logi("Auto Totem: could not identify the server-side player. Not starting.");
    return false;
  }

  g_getOffhand = reinterpret_cast<OffhandFn>(offhand);
  g_getHandContainer = reinterpret_cast<HandContainerFn>(helper);

  g_tickTarget = reinterpret_cast<void *>(tick);
  const int rc = pl::memory::hook(g_tickTarget, reinterpret_cast<void *>(&hook_tick),
                                  reinterpret_cast<void **>(&orig_tick));
  if (rc != 0) {
    __android_log_print(ANDROID_LOG_ERROR, kTag, "Auto Totem: hook failed (code %d).", rc);
    g_tickTarget = nullptr;
    return false;
  }
  g_installed.store(true);
  __android_log_print(ANDROID_LOG_INFO, kTag, "Auto Totem: ready (tick hook at %p).",
                      g_tickTarget);
  return true;
}

void removeAll() {
  g_installed.store(false);
  if (g_tickTarget) {
    pl::memory::unhook(g_tickTarget, reinterpret_cast<void *>(&hook_tick));
  }
  g_tickTarget = nullptr;
  orig_tick = nullptr;
  g_players.clear();
}

// ---- Menu callbacks ------------------------------------------------------------
void onModuleToggle(std::string_view moduleId, bool enabled) {
  if (moduleId != kModule) return;
  if (enabled) {
    if (!installAll()) {
      g_enabled.store(false);
      pl::modmenu::setModuleEnabled(kModule, false);
      return;
    }
    // Learn your totem the moment you switch it on, if you are holding one.
    g_learnRequested.store(true);
  }
  g_enabled.store(enabled);
}

void onButtonEvent(std::string_view buttonId, pl::modmenu::ButtonEvent event, float) {
  if (event != pl::modmenu::ButtonEvent::Click) return;
  if (buttonId == kLearnButton) {
    g_learnRequested.store(true);
    logi("Auto Totem: will learn the item in your offhand on the next tick.");
  }
}

// ---- Mod object -----------------------------------------------------------------
class Moduflux {
public:
  bool load(pl::mod::ModContext &) {
    using namespace pl::modmenu;
    logi("Moduflux: load() started");

    const bool m =
        ModuleBuilder(kModule, "Auto Totem")
            .description("Refills your offhand with another totem when one pops. "
                         "Hold a totem in your offhand, then switch this on. "
                         "Works in worlds hosted on this phone.")
            .defaultEnabled(false)
            .onToggle(onModuleToggle)
            .registerModule();

    const bool b = ButtonBuilder(kLearnButton, "Learn Totem")
                       .moduleId(kModule)
                       .label("LT")
                       .behavior(ButtonBehavior::Click)
                       .stylePreset(ButtonStylePreset::Accent)
                       .onEvent(onButtonEvent)
                       .registerButton();

    logi("Moduflux: loaded");
    return m && b;
  }

  bool enable(pl::mod::ModContext &) {
    logi("Moduflux: enabled (nothing is hooked until Auto Totem is switched on)");
    return true;
  }

  bool disable(pl::mod::ModContext &) {
    g_enabled.store(false);
    removeAll();
    pl::modmenu::unregisterButton(kLearnButton);
    pl::modmenu::unregisterModule(kModule);
    return true;
  }

  bool unload(pl::mod::ModContext &) { return true; }
};

Moduflux g_mod;

} // namespace

PL_REGISTER_MOD(Moduflux, g_mod)

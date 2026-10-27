# Frontier — Territorial Expansion

A fast-paced browser territorial expansion strategy game built with Vanilla JavaScript, HTML5 Canvas, and CSS. No external dependencies required.

## Features
- **Procedural Map Generation**: Dynamic grid terrain with impassable mountain obstacles and balanced spawn points.
- **Dynamic Faction AI**: Compete against 3 AI opponents with distinct personalities (Aggressive, Defensive, Economic).
- **Territorial Combat & Frontlines**: Real-time border wars where defense scales based on border length and troop count.
- **Economy & Infrastructure**:
  - **Cities**: Boost troop capacity and territorial defense.
  - **Defense Posts**: Project defensive force multipliers to nearby cells.
  - **Missile Silos & Nukes**: Strategic area-denial strikes leaving lingering fallout.
  - **Factories & Trains**: Connect infrastructure to generate gold income.
- **Diplomatic Relations**: Form alliances, coordinate peace, or execute tactical betrayals (with traitor penalties).

## How to Run
Simply open `index.html` in any modern web browser, or serve it locally:

```bash
# Using Python
python3 -m http.server 8000
```

Then navigate to `http://localhost:8000`.

## Controls
- **Left Click**: Expand into adjacent neutral territory, attack neighbouring enemy factions, or place selected buildings.
- **Right Click / Esc**: Cancel active build or targeting mode.
- **Space**: Pause / Resume game.
- **1 - 4**: Quick select City, Defense Post, Missile Silo, or Nuke targeting.
- **5**: Quick recruit troops using gold reserves.

# Парсер Hand History с базовыми HUD-статистиками

`hh_stats.py` — это консольный Python-скрипт для парсинга текстовых **Hand History** (HH) покер-румов и построения базовых **HUD-статистик** по игрокам.

Скрипт анализирует файлы HH (PokerStars-подобный формат или generic) и рассчитывает ключевые показатели, которые обычно используются в HUD’ах: VPIP, PFR, 3BET, Fold to CBet и др.  
Результаты сохраняются в **CSV** и/или **JSON**, а также могут быть выведены в консоль в виде краткого отчёта.

---

## 🚀 Возможности

- 📂 Поддержка одиночных файлов HH и директорий с рекурсивным обходом.  
- 🎲 Поддержка форматов **PokerStars (EN)** и generic (MVP).  
- 📊 Подсчёт HUD-метрик:
  - **Preflop:** HANDS, VPIP, PFR, 3BET/OPP, 4BET/OPP, Steal Attempts & Success, Raise First In (RFI) по позициям.  
  - **Postflop:** CBet Flop / Opp, Fold to CBet Flop / Opp.  
  - **Showdown:** Went to Showdown (WTSD), Won $ at Showdown (W$SD).  
  - **Aggression:** AF, Agg% (Aggression Factor, Aggression Percentage).  
  - **Финансовые:** NET (в bb), bb/100.  
- 🔎 Определение позиций игроков: UTG, MP, CO, BTN, SB, BB.  
- 💾 Экспорт в **CSV** и **JSON**.  
- 📑 Краткий консольный отчёт с топ-игроками.  

---

## ⚙️ Установка

1. Убедитесь, что у вас установлен **Python 3.11+**.  
2. Склонируйте репозиторий:
```bash
git clone https://github.com/PokerScripts/Hand-History-HUD.git
cd Hand-History-HUD
````

3. Запустите скрипт напрямую:

```bash
python hh_stats.py --help
```

Зависимости: используется только стандартная библиотека Python (дополнительные пакеты не требуются).

---

## ▶️ Примеры запуска

### 1. Базовый запуск для директории с раздачами

```bash
python hh_stats.py --path ./hands --out stats.csv --show-report
```

### 2. Экспорт JSON + фильтрация по датам

```bash
python hh_stats.py --path ./hands --json-out stats.json --from 2025-01-01 --to 2025-08-22
```

### 3. С разбивкой по позициям

```bash
python hh_stats.py --path ./hands --per-position --show-report
```

---

## 📂 Пример структуры CSV

```csv
player,hands,net_bb,bb100,vpip,vpip_opp,pfr,pfr_opp,threebet,threebet_opp,steal_att,steal_succ,cbet_flop,cbet_flop_opp,fold_to_cbet_flop,fold_to_cbet_flop_opp,wtsd,w$sd,agg_acts,pass_acts,af,agg_pct,rfi_UTG,rfi_UTG_opp,rfi_MP,rfi_MP_opp,rfi_CO,rfi_CO_opp,rfi_BTN,rfi_BTN_opp,rfi_SB,rfi_SB_opp,rfi_BB,rfi_BB_opp
Hero,3120,112.5,3.6,24.8,1250,19.1,950,7.2,600,180,95,210,320,65,120,155,90,450,1180,0.85,32.5,10.5,100,15.2,118,25.1,320,31.7,420,12.0,300,7.2,210
```

---

## 📊 Пример консольного отчёта

```
Players: 42 | Hands: 12,345 | Period: 2025-01-01..2025-08-22 | Files: 87
Top by volume:
   1) Hero        HANDS=3120   VPIP=24.8%  PFR=19.1%  3BET=7.2%   bb/100=3.6
   2) Villain42   HANDS=2870   VPIP=31.0%  PFR=20.5%  3BET=9.8%   bb/100=-2.1
Top by net_bb:
   1) Hero        NET_BB=+112.5   HANDS=3120   bb/100=3.6
   2) PlayerX     NET_BB=+75.3    HANDS=2100   bb/100=3.4
```

---

## 📌 Ограничения MVP

* Поддерживаются **только кэш-игры** (6-max / 9-max), **No-Limit Hold’em**.
* Парсинг **PokerStars (EN)** и generic HH; другие рума — позже.
* WTSD/W\$SD считаются упрощённо (по факту выигрыша банка).
* RFI/STEAL рассчитываются приближённо (мультивей сценарии могут считаться неточно).
* Не учитываются **Straddle / Bomb Pot / Split Pot**.
* Нет мультипоточности — скрипт обрабатывает файлы последовательно.

---

## 🔮 Планы на v0.2+

* Полная поддержка WTSD/W\$SD (с точным парсингом шоудаунов).
* Более точное определение возможностей для 3BET/4BET и RFI.
* Поддержка форматов HH других румов (888poker, PartyPoker, GGpoker).
* Визуализация статистики (heatmap VPIP/PFR, графики bb/100).
* Поддержка MTT/SNG (ICM-статистика, бай-ины, призовые).
* Параллельная обработка файлов для ускорения.

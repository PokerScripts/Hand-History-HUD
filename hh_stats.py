#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
hh_stats.py — Парсер Hand History + базовые HUD-статы (MVP в одном файле)

➡ Возможности:
- Рекурсивный разбор текстовых HH (PokerStars-подобный / generic) из файла или директории.
- Подсчёт базовых HUD-метрик по игрокам: HANDS, VPIP, PFR, 3BET/OPP, 4BET/OPP,
  STEAL_ATT/STEAL_SUCC, CBET_FLOP/OPP, FOLD_TO_CBET_FLOP/OPP, WTSD, W$SD,
  AGG (agg actions), PASS (passive actions), AF, AGG%, NET (в bb), bb/100.
- Разбивка по позициям (UTG/MP/CO/BTN/SB/BB) при --per-position.
- Экспорт CSV и JSON, консольный отчёт.

⚠ Ограничения MVP:
- No-Limit Hold’em, кэш 6-max/9-max (MTT/SNG не распознаются как отдельные форматы).
- Анте поддерживаются, но экзотические опции (страддл/бомб-пот) — нет.
- Поддержка английских HH (ключевые маркеры "*** FLOP ***" и т.д.).
- Разбор денежных величин в $/€ → нормализация в больших блайндах (bb).
"""

from __future__ import annotations

import argparse
import csv
import json
import logging
import re
from collections import defaultdict, Counter
from dataclasses import dataclass, field, asdict
from datetime import datetime
from itertools import chain
from pathlib import Path
from typing import Dict, List, Tuple, Iterable, Optional, Any


# ==========================
# Константы и паттерны
# ==========================

# Регексы для распознавания ключевых блоков HH (под PokerStars/generic)
RE_NEW_HAND = re.compile(r'^(?P<site>PokerStars|.+?) Hand #(?P<id>\d+):', re.IGNORECASE)
RE_DT = re.compile(r' - (?P<dt>[\w\s:/\-\+]+)$')
RE_BLINDS = re.compile(r'Blinds? (?P<sb>[\d\.,]+)/(?P<bb>[\d\.,]+)', re.IGNORECASE)
RE_TABLE_BTN_PS = re.compile(r'^Table .+? Seat #(?P<btn>\d+) is the button', re.IGNORECASE)
RE_TABLE_BTN_GENERIC = re.compile(r'^Table .+? Button Seat (?P<btn>\d+)', re.IGNORECASE)
RE_SEAT = re.compile(
    r'^Seat (?P<seat>\d+): (?P<name>.+?) \((?P<stack_cur>[$€]?)(?P<stack>[\d\.,]+)\s?(in chips)?\)',
    re.IGNORECASE,
)
RE_POST = re.compile(
    r'^(?P<name>.+?) posts (?P<what>small blind|big blind|ante|dead blind) ?(?P<cur>[$€]?)?(?P<amt>[\d\.,]+)',
    re.IGNORECASE,
)
RE_STREET = re.compile(r'^\*{3} (HOLE CARDS|FLOP|TURN|RIVER|SHOW DOWN|SUMMARY) \*{3}', re.IGNORECASE)
RE_BOARD_FLOP = re.compile(r'^\*{3} FLOP \*{3} \[(?P<flop>(?:[2-9TJQKA][cdhs]\s*){3})\]', re.IGNORECASE)
RE_BOARD_TURN = re.compile(
    r'^\*{3} TURN \*{3} \[(?P<flop>.*?)\] \[(?P<card>[2-9TJQKA][cdhs])\]',
    re.IGNORECASE,
)
RE_BOARD_RIVER = re.compile(
    r'^\*{3} RIVER \*{3} \[(?P<turn>.*?)\] \[(?P<card>[2-9TJQKA][cdhs])\]',
    re.IGNORECASE,
)
RE_ACTION = re.compile(
    r'^(?P<name>.+?) (?P<act>checks|folds|calls|bets|raises)(?: (?P<cur>[$€]?)(?P<amt1>[\d\.,]+))?(?: to (?P<cur2>[$€]?)(?P<amt2>[\d\.,]+))?(?P<allin> and is all-in)?',
    re.IGNORECASE,
)
RE_COLLECTED = re.compile(
    r'^(?P<name>.+?) collected (?P<cur>[$€]?)(?P<amt>[\d\.,]+) from pot', re.IGNORECASE
)
RE_RETURNED = re.compile(
    r'^(?P<name>.+?) (?:gets back |returned )(?P<cur>[$€]?)(?P<amt>[\d\.,]+)', re.IGNORECASE
)
RE_SHOWS = re.compile(r'^(?P<name>.+?) shows ', re.IGNORECASE)
RE_MUCKS = re.compile(r'^(?P<name>.+?) mucks ', re.IGNORECASE)

RE_SUMMARY_TOTAL_POT = re.compile(
    r'^Total pot (?P<cur>[$€]?)(?P<amt>[\d\.,]+)', re.IGNORECASE
)
RE_STAKES = re.compile(r'(?P<cur>[$€]?)(?P<bb>[\d\.,]+)\s*NL|NL\s*(?P<cur2>[$€]?)(?P<bb2>[\d\.,]+)', re.IGNORECASE)

POSITIONS_9MAX = ["UTG", "UTG+1", "MP", "MP+1", "CO", "BTN", "SB", "BB"]
POSITIONS_6MAX = ["UTG", "MP", "CO", "BTN", "SB", "BB"]


# ==========================
# Утилиты
# ==========================

def parse_money(s: Optional[str]) -> float:
    """Парсинг денежной суммы вида '$1.25' / '1,25' / '0.5' → float"""
    if not s:
        return 0.0
    s = s.replace(",", "")
    return float(s)


def safe_div(a: float, b: float) -> float:
    return a / b if b else 0.0


def to_iso(dt_str: str) -> str:
    """Пытаемся привести дату к ISO; при неудаче — возвращаем исходное."""
    dt_str = dt_str.strip()
    # Попытка нескольких форматов
    for fmt in ("%Y/%m/%d %H:%M:%S ET", "%Y-%m-%d %H:%M:%S", "%Y/%m/%d %H:%M:%S", "%b %d %Y %H:%M:%S"):
        try:
            return datetime.strptime(dt_str, fmt).isoformat()
        except Exception:
            continue
    return dt_str


def guess_site(block: List[str]) -> str:
    """Грубый детектор сайта по заголовку"""
    for line in block[:3]:
        if RE_NEW_HAND.search(line):
            site = RE_NEW_HAND.search(line).group('site')
            if 'PokerStars' in site:
                return 'pokerstars'
            return 'generic'
    # fallback
    return 'generic'


def human_pos_order(n_players: int) -> List[str]:
    """Возвращает список позиций по количеству игроков (6-max или 9-max).
    Порядок позиционирования в отчёте. Для маппинга конкретных мест используется BTN как опорная точка."""
    return POSITIONS_6MAX if n_players <= 6 else POSITIONS_9MAX


# ==========================
# Структуры данных
# ==========================

@dataclass
class Action:
    street: str               # 'preflop','flop','turn','river'
    actor: str                # имя игрока
    kind: str                 # 'check','fold','call','bet','raise','post_sb','post_bb','post_ante','post_dead'
    amount_to_bb: float = 0.0 # размер ставки "до" (для raise to)
    amount_add_bb: float = 0.0 # инкремент (для call/bet/raise добавленная сумма)
    allin: bool = False


@dataclass
class Hand:
    hand_id: str = ""
    site: str = "generic"
    dt_iso: str = ""
    bb_val: float = 1.0
    sb_val: float = 0.5
    ante_val: float = 0.0
    max_players: int = 6
    btn_seat: Optional[int] = None

    # seats: seat_no -> (name, stack_bb)
    seats: Dict[int, Tuple[str, float]] = field(default_factory=dict)

    # списки действий по улицам
    actions: Dict[str, List[Action]] = field(default_factory=lambda: {
        'preflop': [], 'flop': [], 'turn': [], 'river': []
    })

    board: Dict[str, List[str]] = field(default_factory=lambda: {
        'flop': [], 'turn': [], 'river': []
    })

    # суммы, собранные победителями
    collected_bb: Dict[str, float] = field(default_factory=dict)
    # суммы, возвращённые игрокам (например, излишек)
    returned_bb: Dict[str, float] = field(default_factory=dict)

    # кеш: позиция по игроку (рассчитанная позже)
    positions: Dict[str, str] = field(default_factory=dict)

    # служебное
    status: str = "ok"  # ok|corrupt


@dataclass
class PlayerAgg:
    # Базовые
    hands: int = 0
    net_bb: float = 0.0

    # Префлоп
    vpip: int = 0
    vpip_opp: int = 0
    pfr: int = 0
    pfr_opp: int = 0
    threebet: int = 0
    threebet_opp: int = 0
    fourbet: int = 0
    fourbet_opp: int = 0
    steal_att: int = 0
    steal_succ: int = 0
    rfi_pos: Dict[str, Tuple[int, int]] = field(default_factory=lambda: defaultdict(lambda: [0, 0]))  # pos -> [rfi_cnt, rfi_opp]

    # Постфлоп
    cbet_flop: int = 0
    cbet_flop_opp: int = 0
    fold_to_cbet_flop: int = 0
    fold_to_cbet_flop_opp: int = 0
    wtsd: int = 0
    w$sd: int = 0  # Won $ at Showdown: количество выигранных шоудаунов

    # Агрессия
    agg_acts: int = 0  # bet/raise
    pass_acts: int = 0  # call/check

    # Разбивки
    by_pos: Dict[str, 'PlayerAgg'] = field(default_factory=dict)  # позиция -> вложенная агрегатная структура


# ==========================
# Парсинг рук
# ==========================

def split_blocks(lines: Iterable[str]) -> Iterable[List[str]]:
    """Разбивает поток строк на блоки по раздачам. Новая раздача — по заголовку Hand # или пустой строке между руками."""
    buf: List[str] = []
    for ln in lines:
        line = ln.rstrip("\n")
        if RE_NEW_HAND.match(line) and buf:
            # Новая рука начинается — отдать предыдущую
            yield buf
            buf = [line]
        else:
            # Накапливаем
            if line or buf:
                buf.append(line)
    if buf:
        yield buf


def parse_header_info(block: List[str], hand: Hand) -> None:
    """Парсинг шапки: сайт, id, время, блайнды, лимит, кнопка."""
    # Заголовок
    m = RE_NEW_HAND.search(block[0])
    if m:
        hand.site = 'pokerstars' if 'PokerStars' in m.group('site') else 'generic'
        hand.hand_id = m.group('id')
        # Дата/время в конце заголовка
        mdt = RE_DT.search(block[0])
        hand.dt_iso = to_iso(mdt.group('dt')) if mdt else ""

    # Поиск блайндов и ставок
    sb = bb = None
    for line in block[:5]:
        mb = RE_BLINDS.search(line)
        if mb:
            sb = parse_money(mb.group('sb'))
            bb = parse_money(mb.group('bb'))
            break
        # Альтернативный способ вычленить bb из "NL"
        ms = RE_STAKES.search(line)
        if ms:
            bb = parse_money(ms.group('bb') or ms.group('bb2'))
            # sb не всегда явно указан, предположим 0.5 bb
            sb = bb / 2.0 if bb else None

    if bb:
        hand.bb_val = bb
        hand.sb_val = sb or (bb / 2.0)

    # Кнопка
    btn = None
    for line in block[:8]:
        m1 = RE_TABLE_BTN_PS.search(line)
        m2 = RE_TABLE_BTN_GENERIC.search(line)
        if m1:
            btn = int(m1.group('btn'))
            break
        if m2:
            btn = int(m2.group('btn'))
            break
    hand.btn_seat = btn


def parse_seats(block: List[str], hand: Hand) -> None:
    """Парсинг сидений и стэков."""
    for line in block:
        ms = RE_SEAT.match(line)
        if ms:
            seat = int(ms.group('seat'))
            name = ms.group('name').strip()
            stack = parse_money(ms.group('stack'))
            stack_bb = stack / hand.bb_val if hand.bb_val else 0.0
            hand.seats[seat] = (name, stack_bb)
    # максимум игроков
    hand.max_players = max(6, len(hand.seats))


def parse_board(line: str, hand: Hand) -> None:
    if m := RE_BOARD_FLOP.match(line):
        cards = m.group('flop').strip().split()
        hand.board['flop'] = cards
    elif m := RE_BOARD_TURN.match(line):
        prev = m.group('flop')
        # Извлекаем 3 карты с флопа из скобок
        flop_cards = re.findall(r'([2-9TJQKA][cdhs])', prev)
        turn_card = m.group('card')
        hand.board['flop'] = flop_cards
        hand.board['turn'] = [turn_card]
    elif m := RE_BOARD_RIVER.match(line):
        prev = m.group('turn')
        turn_cards = re.findall(r'([2-9TJQKA][cdhs])', prev)
        river_card = m.group('card')
        # prev обычно "[Ah Kd Qs] [2c]" — достанем все
        all_prev = re.findall(r'([2-9TJQKA][cdhs])', prev)
        if len(all_prev) >= 4:
            hand.board['flop'] = all_prev[:3]
            hand.board['turn'] = [all_prev[3]]
        else:
            # fallback
            if 'flop' not in hand.board or not hand.board['flop']:
                hand.board['flop'] = turn_cards[:3]
            hand.board['turn'] = [turn_cards[-1]] if turn_cards else hand.board.get('turn', [])
        hand.board['river'] = [river_card]


def normalize_action(line: str, current_street: str, hand: Hand) -> Optional[Action]:
    """Нормализуем строку действия в Action. Возвращаем None, если не похоже на действие."""
    # Постинги блайндов/ант
    mp = RE_POST.match(line)
    if mp:
        name = mp.group('name').strip()
        what = mp.group('what').lower()
        amt = parse_money(mp.group('amt'))
        amt_bb = amt / hand.bb_val if hand.bb_val else amt
        kind_map = {
            'small blind': 'post_sb',
            'big blind': 'post_bb',
            'ante': 'post_ante',
            'dead blind': 'post_dead',
        }
        return Action(street='preflop', actor=name, kind=kind_map.get(what, 'post'), amount_add_bb=amt_bb)

    ma = RE_ACTION.match(line)
    if ma:
        name = ma.group('name').strip()
        act = ma.group('act').lower()
        amt1 = parse_money(ma.group('amt1')) if ma.group('amt1') else 0.0
        amt2 = parse_money(ma.group('amt2')) if ma.group('amt2') else 0.0
        allin = bool(ma.group('allin'))
        # Нормализация сумм в bb
        amt1_bb = amt1 / hand.bb_val if hand.bb_val else amt1
        amt2_bb = amt2 / hand.bb_val if hand.bb_val else amt2

        if act == 'checks':
            return Action(current_street, name, 'check', 0.0, 0.0, allin)
        if act == 'folds':
            return Action(current_street, name, 'fold', 0.0, 0.0, allin)
        if act == 'calls':
            return Action(current_street, name, 'call', 0.0, amt1_bb, allin)
        if act == 'bets':
            return Action(current_street, name, 'bet', amt1_bb, amt1_bb, allin)
        if act == 'raises':
            # raise to X: amount_to_bb = X; amount_add_bb = (X - previous_player_commit) будет посчитано позже
            return Action(current_street, name, 'raise', amt2_bb if amt2_bb else amt1_bb, 0.0, allin)

    mc = RE_COLLECTED.match(line)
    if mc:
        name = mc.group('name').strip()
        amt = parse_money(mc.group('amt'))
        hand.collected_bb[name] = hand.collected_bb.get(name, 0.0) + (amt / hand.bb_val if hand.bb_val else amt)
        return None

    mr = RE_RETURNED.match(line)
    if mr:
        name = mr.group('name').strip()
        amt = parse_money(mr.group('amt'))
        hand.returned_bb[name] = hand.returned_bb.get(name, 0.0) + (amt / hand.bb_val if hand.bb_val else amt)
        return None

    # Игнорируем строки шоудауна/массировки
    if RE_SHOWS.match(line) or RE_MUCKS.match(line) or RE_SUMMARY_TOTAL_POT.match(line):
        return None

    return None


def parse_hand_block(block: List[str]) -> Hand:
    """Разбор одного блока раздачи в структуру Hand."""
    hand = Hand()
    try:
        parse_header_info(block, hand)
        parse_seats(block, hand)

        street = 'preflop'
        for line in block:
            if RE_STREET.match(line):
                tag = line.split('***')[1].strip().lower()
                if 'hole cards' in tag:
                    street = 'preflop'
                elif 'flop' in tag:
                    street = 'flop'
                elif 'turn' in tag:
                    street = 'turn'
                elif 'river' in tag:
                    street = 'river'
                else:
                    # show down / summary — действий больше нет
                    street = street
                # Одновременно попробуем вытащить борд
                parse_board(line, hand)
                continue

            # Действия/постинги/результаты
            act = normalize_action(line, street, hand)
            if act:
                # raise: amount_add_bb посчитаем позже при нормализации пота
                hand.actions[act.street].append(act)
    except Exception as e:
        logging.exception("Ошибка при парсинге руки: %s", e)
        hand.status = "corrupt"
    return hand


# ==========================
# Позиции и возможности
# ==========================

def build_positions(hand: Hand) -> None:
    """Выставляем позиции (UTG..BTN..SB..BB) относительно кнопки.
    Привязка по порядку сидений по часовой стрелке."""
    if not hand.btn_seat or not hand.seats:
        return
    seats_sorted = sorted(hand.seats.keys())
    # Сформируем порядок игроков начиная от BTN
    # На PokerStars места идут по кругу: BTN -> SB -> BB -> UTG -> ... -> BTN
    # Находим индекс BTN в отсортированном списке, строим круговой порядок
    if hand.btn_seat not in seats_sorted:
        return

    idx_btn = seats_sorted.index(hand.btn_seat)
    circle = seats_sorted[idx_btn:] + seats_sorted[:idx_btn]

    # Маппинг мест по кругу: BTN, SB, BB, UTG...
    # Далее позиции префлоп: после BB идёт UTG и далее по порядку активных игроков
    players = [hand.seats[s][0] for s in circle]  # имена в порядке от BTN
    n = len(players)
    pos_order = human_pos_order(n)

    # Определим позиции:
    # index 0 -> BTN
    # 1 -> SB
    # 2 -> BB
    # остальные -> UTG, UTG+1/MP...
    position_map = {}
    if n >= 1:
        position_map[players[0]] = 'BTN'
    if n >= 2:
        position_map[players[1]] = 'SB'
    if n >= 3:
        position_map[players[2]] = 'BB'
    remaining = players[3:]
    # Левая часть позиций (до CO) — берём из начала списка соответствующего формата
    pos_linear = [p for p in pos_order if p not in ('BTN', 'SB', 'BB')]
    # Сопоставляем оставшиеся места слева направо
    for i, name in enumerate(remaining):
        position_map[name] = pos_linear[i] if i < len(pos_linear) else pos_linear[-1]

    hand.positions = position_map


# ==========================
# Подсчёт пота и инвестиций
# ==========================

def compute_investments(hand: Hand) -> Dict[str, float]:
    """Подсчитываем, сколько bb каждый игрок вложил в банк за всю руку.
    Для raise используем amount_to_bb, пересчитывая инкременты по текущему уставленному уровню на улице.
    Возвращаем dict: player -> invested_bb (за вычетом возвращённых)."""
    invested = Counter()  # name -> bb

    # Постинги (preflop) уже как amount_add_bb
    for a in hand.actions['preflop']:
        if a.kind.startswith('post_'):
            invested[a.actor] += a.amount_add_bb

    # Функция обработки линии улицы, учитывая текущую "требуемую" сумму на колл
    def handle_street(street_name: str):
        # Какие игроки сколько уже вложили на этой улице (для подсчёта raise to)
        committed = Counter()
        required_to_call = 0.0
        for a in hand.actions[street_name]:
            k = a.kind
            if k == 'check' or k == 'fold':
                # вложений нет
                continue
            if k == 'call':
                # колл доплачивает разницу до required_to_call
                pay = max(0.0, required_to_call - committed[a.actor])
                invested[a.actor] += pay
                committed[a.actor] += pay
            elif k == 'bet':
                # первая ставка на улице
                # bet X: игрок доплачивает X поверх committed (который обычно 0)
                invested[a.actor] += a.amount_add_bb
                committed[a.actor] += a.amount_add_bb
                required_to_call = committed[a.actor]
            elif k == 'raise':
                # raise to Y: увеличение требуемой суммы до Y
                # Игрок должен доплатить Y - committed[actor]
                pay = max(0.0, a.amount_to_bb - committed[a.actor])
                invested[a.actor] += pay
                committed[a.actor] += pay
                required_to_call = max(required_to_call, a.amount_to_bb)
            else:
                # прочее игнор
                pass

    handle_street('preflop')
    handle_street('flop')
    handle_street('turn')
    handle_street('river')

    # Возвраты
    for name, ret in hand.returned_bb.items():
        invested[name] -= ret

    return dict(invested)


# ==========================
# Подсчёт метрик и возможностей
# ==========================

def is_raise_event(a: Action) -> bool:
    return a.kind in ('bet', 'raise')


def is_aggressive(a: Action) -> bool:
    return a.kind in ('bet', 'raise')


def is_passive(a: Action) -> bool:
    return a.kind in ('call', 'check')


def preflop_timeline(hand: Hand) -> List[Action]:
    return [a for a in hand.actions['preflop'] if not a.kind.startswith('post_')]


def compute_preflop_opportunities(hand: Hand, players_in_hand: List[str]) -> Dict[str, Dict[str, bool]]:
    """Определяем базовые возможности на префлопе: VPIP_opp, PFR_opp, 3BET_opp, 4BET_opp и RFI opp."""
    opp = {p: {'vpip': False, 'pfr': False, '3bet': False, '4bet': False, 'rfi': False, 'steal': False} for p in players_in_hand}
    timeline = preflop_timeline(hand)

    # Определение RFI и STEAL: если до игрока все сфолдили/чекнули (не релевантно префлоп) — первый рейз (open)
    # STEAL только для CO/BTN/SB при фолдах до него.
    folded_before = set()
    has_raise = False
    raisers = []  # список игроков, делавших рейз по порядку

    # Кто ещё не пасанул и дошёл до решения — тот имеет VPIP opportunity
    seen_turn = set()

    for a in timeline:
        actor = a.actor
        seen_turn.add(actor)
        # VPIP opportunity — каждому, кто получил ход на префлопе (исключая автопостинги)
        opp[actor]['vpip'] = True

        if a.kind == 'fold':
            folded_before.add(actor)
        elif a.kind == 'call':
            # PFR_opp верно для всех, кто ходил до первого рейза
            if not has_raise:
                opp[actor]['pfr'] = True
        elif a.kind == 'bet' or a.kind == 'raise':
            if not has_raise:
                # это первый рейз — open (RFI opportunity/возможность была у всех, кто ходил)
                has_raise = True
                raisers.append(actor)
                for p in seen_turn:
                    opp[p]['pfr'] = True  # у всех, кто мог сделать первый рейз
                # RFI: если до игрока все сфолдили, и позиция поздняя — считаем как возможность стилла и RFI
                # Для простоты, RFI opportunity будет только у самого рейзера (для процента RFI-by-pos)
                opp[actor]['rfi'] = True
                # STEAL opportunity: если позиция CO/BTN/SB и до него все сфолдили
                pos = hand.positions.get(actor, '')
                if pos in ('CO', 'BTN', 'SB'):
                    # Проверим, что до рейзера никто не входил в раздачу коллом/лимпом
                    # Примем упрощение: если это первый агрессивный ход и seen_turn до этого были только fold — стилл возможен
                    only_folds = all(x in folded_before for x in seen_turn if x != actor)
                    if only_folds:
                        opp[actor]['steal'] = True
            else:
                # это 3бет или 4бет
                if len(raisers) == 1:
                    # второй рейз в раздаче = 3бет
                    for p in players_in_hand:
                        # возможность 3бета есть у всех, кто ещё не действовал после первого рейза?
                        # Упрощённо: тот, кто сделал второй рейз — реализовал; остальные, кому дошла очередь после первого рейза — тоже получат opp в момент их хода.
                        pass
                    opp[actor]['3bet'] = True
                    raisers.append(actor)
                elif len(raisers) == 2:
                    opp[actor]['4bet'] = True
                    raisers.append(actor)
                else:
                    # 5бет+ игнорим в MVP
                    raisers.append(actor)

    # Для простоты: 3BET_opp — всем, кто получил возможность действовать после первого рейза (и до закрытия улицы),
    # 4BET_opp — всем, кто получил возможность действовать после 3бета.
    # Реализация: пройдём ещё раз таймлайн и поставим флаги "когда на столе уже было N-ое повышение"
    has_first_raise = False
    has_second_raise = False
    seen_after_1 = set()
    seen_after_2 = set()
    for a in timeline:
        actor = a.actor
        if a.kind in ('bet', 'raise'):
            if not has_first_raise:
                has_first_raise = True
            elif not has_second_raise:
                has_second_raise = True
        else:
            # call/fold/check — это "ход" тоже
            pass

        if has_first_raise:
            seen_after_1.add(actor)
        if has_second_raise:
            seen_after_2.add(actor)

    for p in seen_after_1:
        opp[p]['3bet'] = True
    for p in seen_after_2:
        opp[p]['4bet'] = True

    return opp


def compute_cbet_flop(hand: Hand, players_in_hand: List[str]) -> Tuple[Optional[str], Dict[str, bool], Dict[str, bool]]:
    """Вычисляем префлоп-агрессора и возможности/события для cbet на флопе.
    Возвращает: (aggressor, cbet_opp_flags, fold_to_cbet_opp_flags)
    cbet_opp[player] = True означает, что у игрока была возможность сделать кбет на флопе (только у агрессора).
    fold_to_cbet_opp[player] = True — у игрока была возможность столкнуться с кбетом (видел флоп против агрессора)."""
    # Определяем последнего агрессора префлоп (последний bet/raise на префлопе)
    aggr = None
    for a in hand.actions['preflop']:
        if a.kind in ('bet', 'raise'):
            aggr = a.actor
    if not aggr:
        return None, {}, {}

    saw_flop_players = set()
    if hand.board['flop']:
        # 플레이еры, которые не сфолдили до конца префлопа (те, кто действовал на флопе + агрессор, если он не перестал участвовать)
        # Для надёжности возьмём список акторов на флопе + агрессор
        saw_flop_players = set([act.actor for act in hand.actions['flop']]) | {aggr}

    cbet_opp = {p: False for p in players_in_hand}
    fold_to_cbet_opp = {p: False for p in players_in_hand}

    if not saw_flop_players:
        return aggr, cbet_opp, fold_to_cbet_opp

    # Возможность кбета — у агрессора, если до него на флопе никто не поставил (первый ход)
    # Для простоты: если агрессор сделал bet/raise на флопе первым ходом — это cbet факт.
    # opp: ставим True всегда, если агрессор увидел флоп.
    if aggr in saw_flop_players:
        cbet_opp[aggr] = True

    # Возможность столкнуться с cbet — у остальных, кто видел флоп
    for p in saw_flop_players:
        if p != aggr:
            fold_to_cbet_opp[p] = True

    return aggr, cbet_opp, fold_to_cbet_opp


def update_stats_with_hand(hand: Hand, stats: Dict[str, PlayerAgg], per_position: bool = False) -> None:
    """Обновляем агрегаты по игрокам согласно разобранной руке."""
    if hand.status != "ok" or not hand.seats:
        return

    # Участники (получили карты) — все из hand.seats
    players = [nm for _, (nm, _) in sorted(hand.seats.items(), key=lambda x: x[0])]
    for p in players:
        stats.setdefault(p, PlayerAgg())
        stats[p].hands += 1

    # Подсчёт инвестиций/выигрышей → NET
    invested = compute_investments(hand)
    winners = hand.collected_bb

    # Начисление NET: победители получают +collected - invested, остальные -invested
    invested_names = set(invested.keys())
    winners_names = set(winners.keys())

    all_names = set(players) | invested_names | winners_names
    for name in all_names:
        win = winners.get(name, 0.0)
        inv = invested.get(name, 0.0)
        delta = win - inv
        stats[name].net_bb += delta

    # Позиции
    build_positions(hand)
    pos_map = hand.positions

    # --- Префлоп метрики ---
    # Возможности
    opp = compute_preflop_opportunities(hand, players)
    # Факты действий
    timeline = preflop_timeline(hand)
    first_raise_done = False
    first_raiser = None

    for a in timeline:
        actor = a.actor
        # VPIP: добровольный вклад (call/raise/bet/limp). В префлопе 'bet' редок (бомб-поты), но учтём.
        if a.kind in ('call', 'bet', 'raise'):
            stats[actor].vpip += 1
        # PFR: первый рейз префлоп
        if a.kind in ('bet', 'raise') and not first_raise_done:
            stats[actor].pfr += 1
            first_raise_done = True
            first_raiser = actor
            # RFI by position (Raise First In) — рейзер без лимперов до него
            # Упростим: если это самый первый агрессивный ход (и до него не было колла), считаем RFI
            if pos_map.get(actor):
                rec = stats[actor].rfi_pos[pos_map[actor]]
                rec[1] += 1  # opportunity
                rec[0] += 1  # fact
        elif a.kind in ('bet', 'raise'):
            # Следующие рейзы: 3бет/4бет факты
            # Определим номер рейза
            # Считаем: второй агрессивный ход = 3бет, третий = 4бет
            # Это приближение (мультивей может смещать), но для MVP достаточно.
            if first_raise_done and actor != first_raiser:
                # Найдём количество raise до текущего момента
                raises_before = sum(1 for x in timeline if x is not a and x.kind in ('bet', 'raise'))
                # Слишком грубо; используем простой счётчик «сколько разных игроков уже рейзили»
                pass

    # Возможности и дополнительные счётчики префлоп
    for p in players:
        if opp[p]['vpip']:
            stats[p].vpip_opp += 1
        if opp[p]['pfr']:
            stats[p].pfr_opp += 1
        if opp[p]['3bet']:
            stats[p].threebet_opp += 1
        if opp[p]['4bet']:
            stats[p].fourbet_opp += 1
        # RFI opportunity — считаем только когда игрок в позиции и первый агрессор (см. выше)
        # STEAL: если opp[p]['steal'] — при первом рейзе с поздней позиции и фолдах до
        if opp[p]['steal']:
            stats[p].steal_att += 1  # opportunity = факт попытки стилла
            # успех стилла: если все сфолдили и банк без сопротивления — определить сложно без спец. маркера
            # Приближение: на префлопе после его рейза нет коллов/3бетов → успех
            # Реализуем ниже после анализа таймлайна.

    # Детектируем попытки стилла и успех (упрощённо)
    # Алгоритм: найдём первого рейзера; если его позиция CO/BTN/SB и до конца префлопа больше не было коллов/рейзов, считаем успех
    if first_raiser and pos_map.get(first_raiser) in ('CO', 'BTN', 'SB'):
        # Были ли ответы?
        after_first = False
        had_defense = False
        for a in timeline:
            if not after_first:
                if a.actor == first_raiser and a.kind in ('bet', 'raise'):
                    after_first = True
                continue
            if a.kind in ('call', 'bet', 'raise'):
                had_defense = True
                break
        if not had_defense:
            stats[first_raiser].steal_succ += 1

    # 3бет/4бет факты (более стабильный способ): пройдём ещё раз и считаем порядки рейзов
    raise_count = 0
    for a in timeline:
        if a.kind in ('bet', 'raise'):
            raise_count += 1
            if raise_count == 2:
                stats[a.actor].threebet += 1
            elif raise_count == 3:
                stats[a.actor].fourbet += 1

    # RFI opportunities для позиций: если игрок — первый рейзер, мы уже учли; но нужно учесть и «opp» для других рук в этой позиции.
    # Для простоты: если игрок находился в позиции и дошёл до решения до первого рейза, считаем возможность RFI.
    # (Это приближение, достаточное для MVP.)
    seen = set()
    first_raise_seen = False
    for a in timeline:
        if not first_raise_seen:
            # Всем, кто дошёл до решения до первого рейза, увеличим opp для их позиции
            pos = pos_map.get(a.actor)
            if pos:
                rec = stats[a.actor].rfi_pos[pos]
                rec[1] += 1  # opportunity
        if a.kind in ('bet', 'raise'):
            first_raise_seen = True

    # --- Постфлоп метрики: CBet flop / Fold to CBet flop ---
    aggr, cbet_opp, fold_to_cbet_opp = compute_cbet_flop(hand, players)
    if aggr:
        if cbet_opp.get(aggr):
            stats[aggr].cbet_flop_opp += 1
        # Факт CBet: если первый агрессивный ход на флопе сделал агрессор
        flop_actions = hand.actions['flop']
        first_aggr_on_flop = next((x for x in flop_actions if x.kind in ('bet', 'raise')), None)
        if first_aggr_on_flop and first_aggr_on_flop.actor == aggr:
            stats[aggr].cbet_flop += 1

        # Fold to CBet opportunities и факты
        for a in flop_actions:
            if fold_to_cbet_opp.get(a.actor):
                # У игрока была возможность столкнуться с кбетом; факт фолда именно на кбет — если первым агр. ходом был кбет, и игрок сфолдил до другого агр. действия
                stats[a.actor].fold_to_cbet_flop_opp += 1
        # Факт fold to CBet: если игрок, встретив кбет (агрессор поставил), сфолдил прежде чем кто-то ещё поставил/рейзнул
        if first_aggr_on_flop and first_aggr_on_flop.actor == aggr:
            # Все действия после кбета до следующего агр. действия
            after = False
            for a in flop_actions:
                if a is first_aggr_on_flop:
                    after = True
                    continue
                if not after:
                    continue
                if a.kind == 'fold':
                    stats[a.actor].fold_to_cbet_flop += 1
                if a.kind in ('bet', 'raise'):
                    break  # дальше уже не чистая реакция на кбет

    # WTSD / W$SD: наивная оценка — если были строки SHOWS и COLLECTED
    # Пройдём по игрокам: если игрок есть в collected или встречается 'shows' — дошёл до шоудауна
    shows = set()
    for line in chain.from_iterable(hand.actions.values()):  # это только Action, но shows — не Action
        pass  # у нас нет данных show в Action; поэтому определим WTSD по факту наличия действий на ривере или collected
    # Упростим: WTSD = игрок в winners OR игрок действовал на ривере (видел ривер и дошёл до вскрытия? слишком грубо)
    # Для MVP: WTSD — все из winners_names; W$SD — те же (выигравшие). Это консервативно.
    for p in winners_names:
        stats[p].wtsd += 1
        stats[p].w$sd += 1

    # Агрессия: считаем сумму агрессивных и пассивных действий по всем улицам
    for st in ('preflop', 'flop', 'turn', 'river'):
        for a in hand.actions[st]:
            if is_aggressive(a):
                stats[a.actor].agg_acts += 1
            elif is_passive(a):
                stats[a.actor].pass_acts += 1

    # Разбивка по позициям (минимальная): приплюсуем только HANDS и bb/NET к вложенным агрегатам
    if per_position:
        for p in players:
            pos = pos_map.get(p, None)
            if not pos:
                continue
            if pos not in stats[p].by_pos:
                stats[p].by_pos[pos] = PlayerAgg()
            sub = stats[p].by_pos[pos]
            sub.hands += 1
            sub.net_bb += invested.get(p, 0.0) * 0.0 + (winners.get(p, 0.0) - invested.get(p, 0.0))  # такой же delta


# ==========================
# Экспорт и отчёт
# ==========================

def finalize_metrics(stats: Dict[str, PlayerAgg]) -> None:
    """Производные метрики (bb/100, AF, AGG%). Доля метрик остаётся в виде счетчиков + opp."""
    for p, s in stats.items():
        # bb/100
        s.bb100 = safe_div(s.net_bb * 100.0, s.hands) if s.hands else 0.0  # добавим динамически атрибут
        # AF/AGG%
        s.af = safe_div(s.agg_acts, max(1, s.pass_acts))
        total = s.agg_acts + s.pass_acts
        s.agg_pct = safe_div(s.agg_acts, total) * 100.0 if total else 0.0


def stats_to_csv(stats: Dict[str, PlayerAgg], path: Path) -> None:
    fields = [
        "player", "hands", "net_bb", "bb100",
        "vpip", "vpip_opp", "pfr", "pfr_opp",
        "threebet", "threebet_opp", "fourbet", "fourbet_opp",
        "steal_att", "steal_succ",
        "cbet_flop", "cbet_flop_opp",
        "fold_to_cbet_flop", "fold_to_cbet_flop_opp",
        "wtsd", "w$sd",
        "agg_acts", "pass_acts", "af", "agg_pct",
        # RFI by pos (минимум)
        "rfi_UTG", "rfi_UTG_opp",
        "rfi_MP", "rfi_MP_opp",
        "rfi_CO", "rfi_CO_opp",
        "rfi_BTN", "rfi_BTN_opp",
        "rfi_SB", "rfi_SB_opp",
        "rfi_BB", "rfi_BB_opp",
    ]
    with path.open("w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=fields)
        w.writeheader()
        for p, s in sorted(stats.items(), key=lambda kv: (-kv[1].hands, kv[0].lower())):
            row = {
                "player": p, "hands": s.hands, "net_bb": round(s.net_bb, 3), "bb100": round(getattr(s, 'bb100', 0.0), 2),
                "vpip": percent(s.vpip, s.vpip_opp), "vpip_opp": s.vpip_opp,
                "pfr": percent(s.pfr, s.pfr_opp), "pfr_opp": s.pfr_opp,
                "threebet": percent(s.threebet, s.threebet_opp), "threebet_opp": s.threebet_opp,
                "fourbet": percent(s.fourbet, s.fourbet_opp), "fourbet_opp": s.fourbet_opp,
                "steal_att": s.steal_att, "steal_succ": s.steal_succ,
                "cbet_flop": percent(s.cbet_flop, s.cbet_flop_opp), "cbet_flop_opp": s.cbet_flop_opp,
                "fold_to_cbet_flop": percent(s.fold_to_cbet_flop, s.fold_to_cbet_flop_opp),
                "fold_to_cbet_flop_opp": s.fold_to_cbet_flop_opp,
                "wtsd": s.wtsd, "w$sd": s.w$sd,
                "agg_acts": s.agg_acts, "pass_acts": s.pass_acts,
                "af": round(getattr(s, 'af', 0.0), 2), "agg_pct": round(getattr(s, 'agg_pct', 0.0), 2),
            }
            # RFI по позициям
            for pos in ("UTG", "MP", "CO", "BTN", "SB", "BB"):
                c, o = s.rfi_pos[pos] if pos in s.rfi_pos else (0, 0)
                row[f"rfi_{pos}"] = percent(c, o)
                row[f"rfi_{pos}_opp"] = o
            w.writerow(row)


def percent(cnt: int, opp: int) -> float:
    return round(safe_div(cnt, opp) * 100.0, 2) if opp else 0.0


def stats_to_json(stats: Dict[str, PlayerAgg], meta: Dict[str, Any], path: Optional[Path]) -> str:
    payload = {
        "meta": meta,
        "players": []
    }
    for p, s in sorted(stats.items(), key=lambda kv: (-kv[1].hands, kv[0].lower())):
        entry = {
            "name": p,
            "overall": {
                "hands": s.hands,
                "net_bb": round(s.net_bb, 3),
                "bb100": round(getattr(s, 'bb100', 0.0), 2),
                "vpip": {"cnt": s.vpip, "opp": s.vpip_opp, "pct": percent(s.vpip, s.vpip_opp)},
                "pfr": {"cnt": s.pfr, "opp": s.pfr_opp, "pct": percent(s.pfr, s.pfr_opp)},
                "threebet": {"cnt": s.threebet, "opp": s.threebet_opp, "pct": percent(s.threebet, s.threebet_opp)},
                "fourbet": {"cnt": s.fourbet, "opp": s.fourbet_opp, "pct": percent(s.fourbet, s.fourbet_opp)},
                "steal": {"att": s.steal_att, "succ": s.steal_succ},
                "cbet_flop": {"cnt": s.cbet_flop, "opp": s.cbet_flop_opp, "pct": percent(s.cbet_flop, s.cbet_flop_opp)},
                "fold_to_cbet_flop": {"cnt": s.fold_to_cbet_flop, "opp": s.fold_to_cbet_flop_opp,
                                      "pct": percent(s.fold_to_cbet_flop, s.fold_to_cbet_flop_opp)},
                "wtsd": s.wtsd, "w$sd": s.w$sd,
                "agg": {"acts": s.agg_acts, "pass": s.pass_acts, "af": round(getattr(s, 'af', 0.0), 2),
                        "agg_pct": round(getattr(s, 'agg_pct', 0.0), 2)},
            },
            "by_pos": {}
        }
        for pos, sub in s.by_pos.items():
            entry["by_pos"][pos] = {
                "hands": sub.hands,
                "net_bb": round(sub.net_bb, 3),
            }
        payload["players"].append(entry)

    js = json.dumps(payload, ensure_ascii=False, indent=2)
    if path:
        path.write_text(js, encoding="utf-8")
    return js


def print_report(stats: Dict[str, PlayerAgg], meta: Dict[str, Any], top: int = 10) -> None:
    total_hands = sum(s.hands for s in stats.values())
    players_n = len(stats)
    print(f"Players: {players_n} | Hands: {total_hands} | Period: {meta.get('from','?')}..{meta.get('to','?')} | Files: {meta.get('files','?')}")
    # Топ по объёму рук
    print("Top by volume:")
    for i, (p, s) in enumerate(sorted(stats.items(), key=lambda kv: (-kv[1].hands, kv[0].lower()))[:top], 1):
        print(f"  {i:>2}) {p:<12} HANDS={s.hands:<5}  VPIP={percent(s.vpip,s.vpip_opp):>5}%  PFR={percent(s.pfr,s.pfr_opp):>5}%  3BET={percent(s.threebet,s.threebet_opp):>5}%  bb/100={round(getattr(s,'bb100',0.0),2):>6}")
    # Топ по прибыли
    print("Top by net_bb:")
    for i, (p, s) in enumerate(sorted(stats.items(), key=lambda kv: (-kv[1].net_bb, kv[0].lower()))[:top], 1):
        print(f"  {i:>2}) {p:<12} NET_BB={round(s.net_bb,2):>8}  HANDS={s.hands:<5}  bb/100={round(getattr(s,'bb100',0.0),2):>6}")


# ==========================
# Чтение файлов и фильтры
# ==========================

def iter_paths(path: Path) -> Iterable[Path]:
    if path.is_file():
        yield path
    else:
        for p in path.rglob("*"):
            if p.is_file() and p.suffix.lower() in (".txt", ".log"):
                yield p


def parse_date(s: Optional[str]) -> Optional[datetime]:
    if not s:
        return None
    try:
        return datetime.fromisoformat(s)
    except Exception:
        try:
            return datetime.strptime(s, "%Y-%m-%d")
        except Exception:
            return None


def hand_in_date_range(hand: Hand, dt_from: Optional[datetime], dt_to: Optional[datetime]) -> bool:
    if not hand.dt_iso or (not dt_from and not dt_to):
        return True
    try:
        dt = datetime.fromisoformat(hand.dt_iso.split(".")[0])
    except Exception:
        return True
    if dt_from and dt < dt_from:
        return False
    if dt_to and dt > dt_to:
        return False
    return True


# ==========================
# Главный пайплайн
# ==========================

def run(args: argparse.Namespace) -> None:
    logging.basicConfig(level=logging.INFO, format="%(levelname)s: %(message)s")

    src = Path(args.path)
    if not src.exists():
        raise SystemExit(f"Не найден путь: {src}")

    stats: Dict[str, PlayerAgg] = {}
    files_cnt = 0
    hands_cnt = 0

    dt_from = parse_date(args.date_from)
    dt_to = parse_date(args.date_to)

    for fp in iter_paths(src):
        files_cnt += 1
        try:
            with fp.open("r", encoding=args.encoding, errors="ignore") as f:
                for block in split_blocks(f):
                    hand = parse_hand_block(block)
                    # Фильтр по дате
                    if not hand_in_date_range(hand, dt_from, dt_to):
                        continue
                    hands_cnt += 1
                    update_stats_with_hand(hand, stats, per_position=args.per_position)
        except Exception as e:
            logging.warning("Ошибка чтения файла %s: %s", fp, e)

        if files_cnt % 50 == 0:
            logging.info("Обработано файлов: %d, рук: %d", files_cnt, hands_cnt)

    finalize_metrics(stats)

    # Экспорт CSV
    if args.out:
        out_path = Path(args.out)
        stats_to_csv(stats, out_path)
        logging.info("CSV сохранён: %s", out_path)

    # Экспорт JSON
    meta = {
        "from": args.date_from or "",
        "to": args.date_to or "",
        "filters": args.filters or "",
        "site": args.site,
        "files": files_cnt,
    }
    if args.json_out:
        json_path = Path(args.json_out)
        stats_to_json(stats, meta, json_path)
        logging.info("JSON сохранён: %s", json_path)

    # Отчёт в консоль
    if args.show_report:
        print_report(stats, meta, top=args.top)


def build_cli() -> argparse.Namespace:
    p = argparse.ArgumentParser(
        description="Парсер HH и агрегатор HUD-статов по игрокам (MVP).",
        formatter_class=argparse.ArgumentDefaultsHelpFormatter,
    )
    p.add_argument("--path", required=True, help="Файл .txt/.log или директория с HH")
    p.add_argument("--site", default="auto", choices=["auto", "pokerstars", "generic"],
                   help="Подсказка формата HH (auto — детект по заголовку)")
    p.add_argument("--out", default="stats.csv", help="Путь для CSV со сводными статами")
    p.add_argument("--json-out", default="", help="Путь для детального JSON (опционально)")
    p.add_argument("--summary", default="", help="Не используется в MVP (зарезервировано)")
    p.add_argument("--from", dest="date_from", default="", help="Дата начала периода YYYY-MM-DD")
    p.add_argument("--to", dest="date_to", default="", help="Дата конца периода YYYY-MM-DD")
    p.add_argument("--filters", default="", help="Фильтры (MVP игнорирует, только для метаданных)")
    p.add_argument("--per-position", action="store_true", help="Разбивка по позициям (минимальная)")
    p.add_argument("--per-street", action="store_true", help="(Зарезервировано) Разбивка по улицам")
    p.add_argument("--top", type=int, default=10, help="Сколько строк показывать в отчёте")
    p.add_argument("--show-report", action="store_true", help="Печатать краткий отчёт в консоль")
    p.add_argument("--seed", type=int, default=0, help="(Зарезервировано) RNG seed")
    p.add_argument("--strict", action="store_true", help="(Зарезервировано) Жёсткий режим ошибок парсинга")
    p.add_argument("--encoding", default="utf-8", help="Кодировка входных файлов")
    return p.parse_args()


if __name__ == "__main__":
    args = build_cli()
    run(args)
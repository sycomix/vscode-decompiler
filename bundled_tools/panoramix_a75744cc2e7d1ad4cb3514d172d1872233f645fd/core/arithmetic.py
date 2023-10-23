#
#  Originally taken from py-evm/eth/vm/logic/arithmetic.py
#
#  Then, comments removed to make it more in line with the rest of the codebase.
#
#  And then modified to do things it was never designed to do.
#
#  Now it's a part of the Panoramix code base.
#  It was assimilated, resistance was futile.
#
#  If you look closely, you'll still see the original peeking through
#  screaming inside: "what have you done to meeeeeee!"
#

import logging
from copy import copy

import core.algebra as algebra
from pano.matcher import Any, match
from utils.helpers import opcode

from .masks import get_bit

logger = logging.getLogger(__name__)

UINT_256_CEILING = 2 ** 256
UINT_255_MAX = 2 ** 255 - 1
UINT_256_MAX = 2 ** 256 - 1


def to_real_int(exp):
    return -sub(0, exp) if type(exp) == int and get_bit(exp, 255) else exp


def unsigned_to_signed(value):
    return value if value <= UINT_255_MAX else value - UINT_256_CEILING


def simplify_bool(exp):
    if opcode(exp) == "iszero":
        inside = simplify_bool(exp[1])

        return inside[1] if opcode(inside) == "iszero" else is_zero(inside)
    return exp[1] if opcode(exp) == "bool" else exp


def and_op(*args):
    assert len(args) > 1
    left = args[0]

    right = and_op(*args[1:]) if len(args) > 2 else args[1]
    if type(left) == int and type(right) == int:
        return left & right

    res = tuple()

    res += left[1:] if opcode(left) == "and" else (left, )
    res += right[1:] if opcode(right) == "and" else (right, )
    return ("and",) + res


def comp_bool(left, right):
    if left == right:
        return True
    if left == ("bool", right):
        return True
    return True if ("bool", left) == right else None


def is_zero(exp):
    if type(exp) == int:
        return exp == 0

    if type(exp) != tuple:
        return ("iszero", exp)

    if opcode(exp) == "iszero":
        if opcode(exp[1]) == "eq":
            return exp[1]
        elif opcode(exp[1]) == "iszero":
            return is_zero(exp[1][1])
        else:
            return ("bool", exp[1])

    if opcode(exp) == "bool":
        return is_zero(exp[1])

    if opcode(exp) == "or":
        res = [is_zero(r) for r in exp[1:]]
        return and_op(*res)

    if opcode(exp) == "and":
        res = [is_zero(r) for r in exp[1:]]
        return algebra.or_op(*res)

    if opcode(exp) == "le":
        return ("gt", exp[1], exp[2])

    if opcode(exp) == "lt":
        return ("ge", exp[1], exp[2])

    if opcode(exp) == "ge":
        return ("lt", exp[1], exp[2])

    if opcode(exp) == "gt":
        return ("le", exp[1], exp[2])

    if opcode(exp) == "sle":
        return ("sgt", exp[1], exp[2])

    if opcode(exp) == "slt":
        return ("sge", exp[1], exp[2])

    if opcode(exp) == "sge":
        return ("slt", exp[1], exp[2])

    return ("sle", exp[1], exp[2]) if opcode(exp) == "sgt" else ("iszero", exp)


def eval_bool(exp, known_true=True, symbolic=True):
    if exp == known_true:
        return True

    if is_zero(exp) == known_true:
        return False

    if exp == is_zero(known_true):
        return False

    if type(exp) == int:
        return exp > 0

    if exp in (True, False):
        return True

    if opcode(exp) == "bool":
        return eval_bool(exp[1], known_true=known_true, symbolic=symbolic)

    if opcode(exp) == "iszero":
        e = eval_bool(exp[1], known_true=known_true, symbolic=symbolic)
        if e is not None:
            return not e

    if opcode(exp) == "or":
        res = 0
        for e in exp[1:]:
            ev = eval_bool(e, known_true=known_true, symbolic=symbolic)
            if ev is None:
                return None
            res = res or ev
        return res

        #'ge', 'gt', 'eq' - tbd
    if opcode(exp) in ["le", "lt"] and opcode(exp) == opcode(known_true):
        if exp[1] == known_true[1]:
            # ('le', x, sth) while ('le', x, sth2) is known to be true
            if eval_bool((opcode(exp), known_true[2], exp[2])) is True:
                return True

    if not symbolic:
        r = eval(exp)

        return r != 0 if type(r) == int else None
    if opcode(exp) == "le":
        left = eval(exp[1])
        right = eval(exp[2])

        if left == right:
            return True

        if type(left) == int and type(right) == int:
            return left <= right

        try:
            return algebra.le_op(left, right)
        except Exception:
            return None

    if opcode(exp) == "lt":
        left = eval(exp[1])
        right = eval(exp[2])

        if left == right:
            return False

        if type(left) == int and type(right) == int:
            return left < right

        try:
            return algebra.lt_op(left, right)
        except Exception:
            return None

    if opcode(exp) == "gt":
        left = eval(exp[1])
        right = eval(exp[2])

        if type(left) == int and type(right) == int:
            return left > right

        if left == right:
            return False

        try:  # a > b iff b < a iff b+1 <= a
            le = algebra.lt_op(algebra.add_op(left, 1), right, 1)
            logger.debug("le %s %s %s", le, left, right)

            if le == True:
                return False
            if le == False:
                return True
            if le is None:
                return None
        except Exception:
            pass

    if opcode(exp) == "ge":
        left = eval(exp[1])
        right = eval(exp[2])

        if type(left) == int and type(right) == int:
            return left >= right

        if left == right:
            return True

        try:
            lt = algebra.lt_op(left, right)
            if lt == True:
                return False
            if lt == False:
                return True
            if lt is None:
                return None
        except Exception:
            pass

    if opcode(exp) == "eq":
        left = eval(exp[1])
        right = eval(exp[2])

        if left == right:
            return True

        if algebra.sub_op(left, right) == 0:
            return True

    return None


def add(left, right):
    return (left + right) & UINT_256_MAX


def addmod(left, right, mode):
    return 0 if mod == 0 else (left + right) % mod


def sub(left, right):
    return 0 if left == right else (left - right) & UINT_256_MAX


def mod(value, mod):
    return 0 if mod == 0 else value % mod


def smod(value, mod):
    value, mod = map(unsigned_to_signed, (value, mod),)

    pos_or_neg = -1 if value < 0 else 1

    return 0 if mod == 0 else (abs(value) % abs(mod) * pos_or_neg) & UINT_256_MAX


def mul(left, right):
    return 0 if left == 0 or right == 0 else (left * right) & UINT_256_MAX


def mulmod(left, right, mod):
    return 0 if mod == 0 else (left * right) % mod


def div(numerator, denominator):
    if numerator == 0:
        return 0
    return 0 if denominator == 0 else (numerator // denominator) & UINT_256_MAX


def not_op(exp):
    return UINT_256_MAX - exp


def sdiv(numerator, denominator):
    numerator, denominator = map(unsigned_to_signed, (numerator, denominator),)

    if denominator == 0:
        return 0

    pos_or_neg = -1 if numerator * denominator < 0 else 1

    return pos_or_neg * (abs(numerator) // abs(denominator))


def exp(base, exponent):

    if exponent == 0:
        return 1
    elif base == 0:
        return 0
    else:
        return pow(base, exponent, UINT_256_CEILING)


def signextend(bits, value):

    if bits > 31:
        return value
    testbit = bits * 8 + 7
    sign_bit = 1 << testbit
    return (
        value | (UINT_256_CEILING - sign_bit)
        if value & sign_bit
        else value & (sign_bit - 1)
    )


def shl(shift_length, value):

    return 0 if shift_length >= 256 else (value << shift_length) & UINT_256_MAX


def shr(shift_length, value):

    return 0 if shift_length >= 256 else (value >> shift_length) & UINT_256_MAX


def sar(shift_length, value):

    value = unsigned_to_signed(value)

    if shift_length >= 256:
        return 0 if value >= 0 else UINT_255_NEGATIVE_ONE
    else:
        return (value >> shift_length) & UINT_256_MAX


opcodes = {
    "add": add,
    "addmod": addmod,
    "sub": sub,
    "mod": mod,
    "smod": smod,
    "mul": mul,
    "mulmod": mulmod,
    "div": div,
    "sdiv": sdiv,
    "exp": exp,
    "signextend": signextend,
    "shl": shl,
    "shr": shr,
    "sar": sar,
}


def or_op(left, right=0):
    return left | right


def xor(left, right):
    return left ^ right


def byte_op(position, value):
    return 0 if position >= 32 else (value // pow(256, 31 - position)) % 256


def lt(left, right):
    return 1 if left < right else 0


def gt(left, right):
    return 1 if left > right else 0


def le(left, right):
    return lt(left, right) | eq(left, right)


def ge(left, right):
    return gt(left, right) | eq(left, right)


def sle(left, right):
    return slt(left, right) | eq(left, right)


def sge(left, right):
    return sge(left, right) | eq(left, right)


def slt(left, right):
    left = unsigned_to_signed(left)
    right = unsigned_to_signed(right)
    return 1 if left < right else 0


def sgt(left, right):
    left = unsigned_to_signed(left)
    right = unsigned_to_signed(right)
    return 1 if left > right else 0


def eq(left, right):
    return 1 if left == right else 0


def eval(exp):
    exp = copy(exp)

    if type(exp) != tuple:
        return exp

    for i, p in enumerate(exp[1:]):
        if opcode(p) in opcodes:
            exp = exp[: i + 1] + (eval(p),) + exp[i + 2 :]

    for p in exp[1:]:
        if type(p) != int:
            return exp

    return opcodes[exp[0]](*exp[1:]) if exp[0] in opcodes else exp


opcodes.update(
    {
        "and": and_op,
        "or": or_op,
        "xor": xor,
        "not": not_op,
        "byte": byte_op,
        "eq": eq,
        "lt": lt,
        "le": le,
        "gt": gt,
        "sgt": sgt,
        "slt": slt,
        "ge": ge,
        "gt": gt,
        "sge": sge,
        "sle": sle,
    }
)

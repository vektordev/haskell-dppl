module JuliaSPPLLib

export safe_log, categorical_index, density_IRUniform, density_IRNormal, cumulative_IRUniform, cumulative_IRNormal, log_density_IRUniform, log_density_IRNormal, log_cumulative_IRUniform, log_cumulative_IRNormal, logsumexp, isAny, InferenceList, EmptyInferenceList, AnyInferenceList, ConsInferenceList, length, getindex, head, tail, prepend, mapList, eq, isPossible, isclose, indexOf, listProd, listConcat, T, Either, Left, Right, fromLeft, fromRight,==


function isAny(x)
    x == "ANY" || x isa AnyInferenceList
end

# Julia's `log` throws a DomainError on a negative argument, where the
# interpreter (Haskell's `log`) answers NaN. Every reachable call site sits
# behind an InjF `applicability` guard today, but that is a property of the
# current inverse set rather than an invariant, so the op is routed through a
# wrapper -- the twin of `safe_log` in `pythonLib.py`. Julia needs no `safe_exp`
# counterpart: `exp(1e6)` already saturates to `Inf`, as Haskell's does.
function safe_log(x)
    if x > 0.0
        return log(x)
    elseif x == 0.0
        return -Inf
    else
        return NaN
    end
end

function density_IRUniform(x)
    if 0.0 <= x <= 1.0
        return 1.0
    else
        return 0.0
    end
end

function cumulative_IRUniform(x)
    if x < 0.0
        return 0.0
    elseif x > 1.0
        return 1.0
    else
        return x
    end
end

function density_IRNormal(x)
    return (1.0 / sqrt(2 * pi)) * exp(-0.5 * x^2)
end

# Phi(x) = erfc(-x / sqrt 2) / 2, through the libm Julia already links
# (openlibm; Base has no erfc and SpecialFunctions is not a dependency). This
# replaced a 5-term Abramowitz-Stegun erf with ~1.5e-7 absolute error, and the
# erfc form, unlike 1 + erf, does not cancel in the lower tail -- where the
# compiler puts every upper tail too, as Phi(-z) (Semiring.upperTailComplement;
# task cumulative-normal-upper-tail-cancellation).
#
# The libm call takes a Float64, so it serves only the types that convert to one
# losslessly. Any other Real -- a ForwardDiff dual number, a BigFloat -- goes
# through `_erfc_generic` instead, written in plain arithmetic so that an AD
# number passes through it and carries its derivative (task
# emitted-runtime-differentiability-gaps; casting it with Float64(x) threw).
const _LibmReal = Union{Base.IEEEFloat, Integer, Rational}

function cumulative_IRNormal(x::_LibmReal)
    return ccall((:erfc, Base.Math.libm), Float64, (Float64,), -Float64(x) / sqrt(2.0)) / 2.0
end

function cumulative_IRNormal(x::Real)
    return _erfc_generic(-x / sqrt(2.0)) / 2.0
end

# erfc in generic arithmetic: the Taylor series of erf for |x| < 1.5 and a
# continued fraction for erfc beyond, which keeps the lower tail free of the
# 1 - erf cancellation. This is the algorithm CPython's math.erfc used before it
# delegated to libm (25 series terms, 50 continued-fraction terms, 0 past 30).
# Within 6e-14 relative of libm over [-8, 27]; the derivative an AD number picks
# up is that of the approximation, within the same order of exp(-x^2) * 2/sqrt(pi).
function _erfc_generic(x)
    ax = abs(x)
    if ax < 1.5
        x2 = x * x
        acc = zero(x2)
        fk = 25.5
        for _ in 1:25
            acc = 2.0 + x2 * acc / fk
            fk -= 1.0
        end
        return 1.0 - acc * x * exp(-x2) / sqrt(pi)
    end
    if ax >= 30.0
        cf = zero(ax)
    else
        x2 = ax * ax
        a = 0.0
        da = 0.5
        p = one(x2); p_last = zero(x2)
        q = da + x2; q_last = one(x2)
        for _ in 1:50
            a += da
            da += 2.0
            b = da + x2
            p, p_last = b * p - a * p_last, p
            q, q_last = b * q - a * q_last, q
        end
        cf = p / q * ax * exp(-x2) / sqrt(pi)
    end
    return x > 0 ? cf : 2.0 - cf
end

# Native log-pdf/log-cdf (task log-space-probability-computation), computed
# directly from the formula rather than as log(density_...(x)): the latter
# would underflow to a true float 0.0 in a deep tail before the log is taken,
# losing the tail entirely.
function log_density_IRUniform(x)
    if 0.0 <= x <= 1.0
        return 0.0
    else
        return -Inf
    end
end

function log_cumulative_IRUniform(x)
    c = cumulative_IRUniform(x)
    return c <= 0.0 ? -Inf : log(c)
end

function log_density_IRNormal(x)
    return -0.5 * x^2 - 0.5 * log(2 * pi)
end

function log_cumulative_IRNormal(x)
    c = cumulative_IRNormal(x)
    return c <= 0.0 ? -Inf : log(c)
end

# Log-sum-exp reduction backing IRLogEnumSum's emitted code: the log-space
# sibling of a plain sum() over enumerated per-value log-probabilities.
function logsumexp(xs)
    xs = collect(xs)
    if isempty(xs)
        return -Inf
    end
    m = maximum(xs)
    if m == -Inf
        return -Inf
    end
    return m + log(sum(exp(x - m) for x in xs))
end

# Inverse-CDF categorical draw backing IR's BCategoricalIndex (task
# neural-categorical-sampler-nests-v-deep): the smallest k in [0, n) with
# u * S < w[start] + ... + w[start + k], S the sum of the n weights, clamped to
# n - 1. `start` and the result are 0-based, as in the IR; `w` is 1-based.
function categorical_index(u, w, start, n)
    total = 0.0
    for k in 1:n
        total += w[start + k]
    end
    target = u * total
    acc = 0.0
    for k in 1:n
        acc += w[start + k]
        if target < acc
            return k - 1
        end
    end
    return n - 1
end

function eq(a, b)
    if isAny(a) || isAny(b)
        return true
    else
        return a == b
    end
end

function isPossible(multiVal, expr)
    tag = multiVal[1]
    if tag == "C"
        return true
    elseif tag == "D"
        return expr in multiVal[2]
    elseif tag == "T" && expr isa T
        sub = multiVal[2]
        return isPossible(sub[1], expr.t1) && isPossible(sub[2], expr.t2)
    elseif tag == "E" && expr isa Left
        return isPossible(multiVal[2][1], fromLeft(expr))
    elseif tag == "E" && expr isa Right
        return isPossible(multiVal[2][2], fromRight(expr))
    elseif tag == "A"
        foundConstr = false
        for c in multiVal[2]
            cName = c[1]
            cMultiFields = c[2]
            if string(typeof(expr)) == cName
                foundConstr = true
                fieldsyms = fieldnames(typeof(expr))
                for (mf, fs) in zip(cMultiFields, fieldsyms)
                    if !isPossible(mf, getfield(expr, fs))
                        return false
                    end
                end
            end
        end
        return foundConstr
    else
        error("Unknown multiVal tag: " * string(multiVal))
    end
end

struct T
    t1
    t2
end

Base.getindex(t::T, i::Int) = begin
    if i == 1
        return t.t1
    elseif i == 2
        return t.t2
    else
        error("Invalid tuple access at element $i")
    end
end

Base.:(==)(other::Any, t::T) = begin
    if !(other isa T)
        return false
    end
    return eq(t.t1, other.t1) && eq(t.t2, other.t2)
end

Base.:(<)(other::Any, t::T) = begin
    if !(other isa T)
        throw(ValueError("Cannot compare Tuple with non-Tuple"))
    end
    return other.t1 < t.t1 && other.t2 < t.t2
end

Base.:(>)(other::Any, t::T) = begin
    if !(other isa T)
        throw(ValueError("Cannot compare Tuple with non-Tuple"))
    end
    return other.t1 > t.t1 && other.t2 > t.t2
end

abstract type Either end

struct Left <: Either 
    val
end
struct Right <: Either 
    val
end
Base.:(==)(other::Any, l::Left) = begin
     if !(other isa Left)
        return false
    end
    return eq(l.val, other.val)
end

Base.:(==)(other::Any, r::Right) = begin
     if !(other isa Right)
        return false
    end
    return eq(r.val, other.val)
end

function fromLeft(l::Either)
    if !(l isa Left)
        throw("parameter is not a Left: " + l)
    else
        return l.val
    end
end

function fromRight(r::Either)
    if !(r isa Right)
        throw("parameter is not a Right: " + r)
    else
        return r.val
    end
end

abstract type InferenceList end

struct EmptyInferenceList <: InferenceList end
struct AnyInferenceList <: InferenceList end
struct ConsInferenceList <: InferenceList
    value
    next
end

Base.length(lst::EmptyInferenceList) = 0
Base.length(lst::AnyInferenceList) = error("Cannot compute length of an AnyList") 
Base.length(lst::ConsInferenceList) = begin
    l = 0
    while (lst isa ConsInferenceList)
        l += 1
        lst = lst.next  
    end
    if (lst isa AnyInferenceList)
        error("Cannot compute length of an AnyList") 
    end
    return l
end

function Base.getindex(lst::InferenceList, i::Int)
    # Walk instead of calling length(lst), which would make every access O(n).
    i >= 1 || throw(BoundsError("Index $i is out of bounds"))
    curr = lst
    while i > 1
        curr isa ConsInferenceList || throw(BoundsError("Index $i is out of bounds"))
        i -= 1
        curr = curr.next
    end
    curr isa ConsInferenceList || throw(BoundsError("Index $i is out of bounds"))

    return curr.value
end

function Base.iterate(lst::InferenceList)
    lst isa ConsInferenceList ? (lst.value, lst.next) : nothing
end

# Base.iterate for subsequent steps
function Base.iterate(lst::InferenceList, state)
    state isa ConsInferenceList ? (state.value, state.next) : nothing
end

Base.:(==)(other::Any, l::InferenceList) = begin
    if !(other isa InferenceList)
        return false
    end
    # An ANY list matches any list on either side, as in the interpreter and
    # pythonLib. head's inverse queries prepend(x, AnyInferenceList()), whose
    # tail is compared against the literal's EmptyInferenceList() tail
    # (task interpreter-eq-nested-tuple-ignores-any).
    if (l isa AnyInferenceList || other isa AnyInferenceList)
        return true
    end
    if (l isa EmptyInferenceList || other isa EmptyInferenceList)
        return l isa EmptyInferenceList && other isa EmptyInferenceList
    end
    return eq(l.value, other.value) && l.next == other.next
end

Base.:(<)(other::Any, l::InferenceList) = begin
    if !(other isa InferenceList)
        throw(ValueError("Cannot compare InferenceList with non-InferenceList"))
    end
    if !(l isa InferenceList)
        throw(ValueError("Cannot compare InferenceList with non-InferenceList"))
    end
    return (head(other) < head(l)) && (tail(other) < tail(l))
end

Base.:(>)(other::Any, l::InferenceList) = begin
    if !(other isa InferenceList)
        throw(ValueError("Cannot compare InferenceList with non-InferenceList"))
    end
    if !(l isa InferenceList)
        throw(ValueError("Cannot compare InferenceList with non-InferenceList"))
    end
    return (head(other) > head(l)) && (tail(other) > tail(l))
end

function prepend(x, xs :: InferenceList) :: InferenceList
    return ConsInferenceList(x, xs)
end

function head(lst::ConsInferenceList)
    lst.value
end
function tail(lst::ConsInferenceList)
    lst.next
end

function mapList(f, lst::EmptyInferenceList)
    return lst
end

function mapList(f, lst::ConsInferenceList)
    val = f(head(lst))
    rst = mapList(f, tail(lst))
    return ConsInferenceList(val, rst)
end

function indexOf(sample, lst::InferenceList)
    if (lst isa EmptyInferenceList || lst isa AnyInferenceList)
        throw(ArgumentError("Element is not in list"))
    end
    if (sample == head(lst))
        return 0
    else
        return 1 + indexOf(sample, tail(lst))
    end
end

function listProd(lst::InferenceList)
    prod(lst)
end

listConcat(lst1::EmptyInferenceList, lst2::InferenceList) = lst2
listConcat(lst1::ConsInferenceList, lst2::InferenceList) =
    ConsInferenceList(head(lst1), listConcat(tail(lst1), lst2))

# Real, not Float64: a dual number (or any AD scalar) reaches it on the float
# path (task emitted-runtime-differentiability-gaps).
function isclose(a::Real, b::Real)
    return abs(a - b) <= 10e-10
end

# NOTE (task retire-irenumsum): `multiValueToValueList` stood here, deriving a
# MultiValue's enumerated support at run time (memoised, because a multi-object
# neural scene's cartesian product dominated the query). Nothing emits a call to
# it any more: an enumerated sum is now a tensor reduce over a map over a
# *literal* list of the domain's values, built at compile time, so the product
# is computed once by the compiler instead of on every query. `isPossible`
# walks the description structurally and never needed it.

end



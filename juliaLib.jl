module JuliaSPPLLib

export density_IRUniform, density_IRNormal, cumulative_IRUniform, cumulative_IRNormal, isAny, InferenceList, EmptyInferenceList, AnyInferenceList, ConsInferenceList, length, getindex, head, tail, prepend, mapList, eq, isclose, indexOf, listProd, T, Either, Left, Right, fromLeft, fromRight,==


function isAny(x)
    x == "ANY" || x isa AnyInferenceList
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

function cumulative_IRNormal(x)
    # Approximation of CDF using error function
    function erf(t::Float64)
        a1, a2, a3, a4, a5 = 0.254829592, -0.284496736, 1.421413741, -1.453152027, 1.061405429
        p = 0.3275911
        sign = t < 0 ? -1.0 : 1.0
        t = abs(t)
        
        t1 = 1.0 / (1.0 + p * t)
        
        return sign * (1.0 - (((((a5 * t1 + a4) * t1) + a3) * t1 + a2) * t1 + a1) * t1 * exp(-t^2))
    end
    
    return 0.5 * (1 + erf(x / sqrt(2)))
end

function eq(a, b)
    if isAny(a) || isAny(b)
        return true
    else
        return a == b
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
    if !(0 < i <= length(lst))
        throw(BoundsError("Index $i is out of bounds"))
    end

    curr = lst
    while i > 1
        i -= 1
        curr = curr.next
    end

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
    if (l isa EmptyInferenceList && other isa EmptyInferenceList)
        return true
    end
    if !(other isa ConsInferenceList)
        if (other isa AnyInferenceList)
            return true
        else
            return false
        end
    end
    if (l isa AnyInferenceList)
        return true
    end
    if !(l isa ConsInferenceList)
        return false
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

function isclose(a::Float64, b::Float64)
    return abs(a - b) <= 10e-10
end

end



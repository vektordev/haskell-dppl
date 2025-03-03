module JuliaSPPLLib

export density_IRUniform, density_IRNormal, cumulative_IRUniform, cumulative_IRNormal, isAny, InferenceList, EmptyInferenceList, AnyInferenceList, ConsInferenceList, length, getindex, head, tail, prepend

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
        lst = lst.next
    end

    return lst.value
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

end

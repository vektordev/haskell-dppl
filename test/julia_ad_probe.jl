# AD-genericity probe for juliaLib.jl and the Julia backend's query-type guard,
# driven by test/TestPythonPrelude.hs (task emitted-runtime-differentiability-gaps).
#
# No Julia AD package is a dependency, so this carries the smallest forward-mode
# dual number that behaves like ForwardDiff's for the purpose: a Real that is
# not an AbstractFloat, with no conversion to Float64. A runtime function that
# casts with Float64(x), or a signature restricted to Float64, refuses it just
# as it refuses a ForwardDiff.Dual.
#
# Usage: julia julia_ad_probe.jl <project root> <emitted module for
#        `main = Normal * 2.0 + 1.0`>
# Exit status 0 on success; otherwise every violation is printed.

include(joinpath(ARGS[1], "juliaLib.jl"))
using .JuliaSPPLLib

struct D <: Real
    v::Float64
    d::Float64
end
D(x::Real) = D(Float64(x), 0.0)
Base.promote_rule(::Type{D}, ::Type{<:Real}) = D
Base.convert(::Type{D}, x::D) = x
Base.convert(::Type{D}, x::Real) = D(x)
Base.:+(a::D, b::D) = D(a.v + b.v, a.d + b.d)
Base.:-(a::D, b::D) = D(a.v - b.v, a.d - b.d)
Base.:-(a::D) = D(-a.v, -a.d)
Base.:*(a::D, b::D) = D(a.v * b.v, a.d * b.v + a.v * b.d)
Base.:/(a::D, b::D) = D(a.v / b.v, (a.d * b.v - a.v * b.d) / (b.v * b.v))
Base.exp(a::D) = D(exp(a.v), exp(a.v) * a.d)
Base.log(a::D) = D(log(a.v), a.d / a.v)
Base.sqrt(a::D) = D(sqrt(a.v), a.d / (2 * sqrt(a.v)))
Base.abs(a::D) = a.v < 0 ? -a : a
Base.:<(a::D, b::D) = a.v < b.v
Base.:<=(a::D, b::D) = a.v <= b.v
Base.:(==)(a::D, b::D) = a.v == b.v
Base.isless(a::D, b::D) = isless(a.v, b.v)
Base.zero(::Type{D}) = D(0.0, 0.0)
Base.one(::Type{D}) = D(1.0, 0.0)
Base.Float64(::D) = error("a dual number was cast to Float64")

include(ARGS[2])

failures = String[]
fail(msg) = push!(failures, msg)
close(a, b, rel) = abs(a - b) <= rel * max(1.0, abs(a), abs(b))

function probe(name, f, x, want_d; rel_d = 1e-9)
    r = try
        f(D(x, 1.0))
    catch e
        fail(name * "(" * string(x) * ") with a dual argument threw: " * sprint(showerror, e))
        return
    end
    if !(r isa D)
        fail(name * "(" * string(x) * ") returned a " * string(typeof(r)) * ": the derivative is lost")
        return
    end
    ref = f(x)
    close(r.v, ref, 1e-12) || fail(name * "(" * string(x) * "): dual value " * string(r.v) * " != float value " * string(ref))
    close(r.d, want_d, rel_d) || fail(name * "(" * string(x) * "): derivative " * string(r.d) * " != " * string(want_d))
end

# Phi' = phi, across the generic erfc's series / continued-fraction boundary
# (|x / sqrt 2| = 1.5 at |x| ~ 2.12) and into both tails.
for x in [-9.0, -4.0, -2.2, -2.0, -0.7, 0.0, 0.3, 2.0, 2.2, 5.0]
    probe("cumulative_IRNormal", cumulative_IRNormal, x, density_IRNormal(x))
end

# The emitted module: the query-type guard admits the dual sample, and the
# density / cdf derivatives are the analytic ones.
pdf(x) = density_IRNormal((x - 1.0) / 2.0) / 2.0
for x in [-3.0, 0.7, 4.5]
    probe("main_prob", s -> main_prob(s)[1], x, -((x - 1.0) / 4.0) * pdf(x))
    probe("main_integ", s -> main_integ(s)[1], x, pdf(x))
end

# isclose takes any Real pair.
try
    isclose(D(0.3, 1.0), 0.3) || fail("isclose(dual 0.3, 0.3) is false")
catch e
    fail("isclose with a dual argument threw: " * sprint(showerror, e))
end

# The guard still refuses what is not one float: an Int and a Bool.
for bad in [1, true]
    try
        main_prob(bad)
        fail("main_prob accepted " * repr(bad))
    catch e
    end
end

if isempty(failures)
    exit(0)
else
    foreach(println, failures)
    exit(1)
end

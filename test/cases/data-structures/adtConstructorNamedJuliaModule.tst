backends: interpreter, julia, python
p(Base)=(0.4, 0.0, False)
p(Main)=(0.3, 0.0, False)
p(Core 0.0)=(0.1196826841204298, 1.0, False)
p(Core ANY)=(0.3, 0.0, False)
-- Constructors named after the modules every Julia module has in scope.
-- Unescaped, struct Base made Julia refuse the module ("invalid redefinition
-- of constant Base"; at top level Core and Main too). Oracle: 0.4, then
-- 0.6 * 0.5 each, and Core 0.0 is 0.3 * phi(0) = 0.3 * 0.3989422804014327.
-- Task adt-constructor-name-shadows-runtime.

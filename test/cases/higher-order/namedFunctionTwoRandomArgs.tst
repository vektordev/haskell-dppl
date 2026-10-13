-- A named function applied to two random arguments, both point witnesses in
-- the returned tuple. Its twin `draw x = Normal in draw y = Normal in (x, y)`
-- answers the same. Was a known issue ("tagged invocation") until task
-- binding-resolver-one-application-rule: the call binds its random leading
-- argument first, in parameter order, as a curried lambda in place does.
-- (ANY, _) is refused at run time: a leading argument's witness is read as an
-- argument of the rest of the call, not in a slot of the observation.
batched
p((0.0, 0.0))=(0.15915494, 2.0, False)
p((0.5, -1.0))=(0.08518950, 2.0, False)
p((0.0, ANY))=(0.39894228, 1.0, False)

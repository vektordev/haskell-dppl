from pythonLib import *
import functools
import math
from torch.nn import Module

# Function group main
# 'main' has 12 correlated observation slots, more than --marginalSlots 4 allows: no per-mask inference variants were compiled for it, so an ANY in one of those slots is answered by the runtime marginal guard alone (which may refuse). Raise --marginalSlots to 12 to compile all 4096 masks.
class Main(Module):
    # Calculates the probability of the sample parameter being less than or equal to the main function
    # Query-type guard active: rejects a query value not matching return type Tuple TBool (ListOf TBool) (disable with --noTypeCheck).
    def integrate(self, sample):
        if (isAny(sample) or (isinstance(sample, T) and (isAny(sample.t1) or isinstance(sample.t1, bool)) and (isAny(sample.t2) or (isinstance(sample.t2, InferenceList) and all((isAny(_ce0) or isinstance(_ce0, bool)) for _ce0 in sample.t2))))):
            if isAny(sample):
                l_1271_any_shared_0 = 1.0
                l_1271_any_shared_1 = False
                l_1271_any_shared = T(l_1271_any_shared_0, l_1271_any_shared_1)
            else:
                _s0 = [True, False]
                _s1 = []
                for _v2 in _s0:
                    if isAny(sample[0]):
                        cse_0 = False
                    elif sample[0]:
                        cse_0 = False
                    else:
                        cse_0 = (not((True if isAny(_v2) else (False == _v2))))
                    if (not(cse_0)):
                        if isAny(sample[1]):
                            l_1267_any_shared_0 = 1.0
                            l_1267_any_shared_1 = False
                            l_1267_any_shared = T(l_1267_any_shared_0, l_1267_any_shared_1)
                        else:
                            if isAny(_v2):
                                cse_2 = True
                            else:
                                cse_2 = (True == _v2)
                            if cse_2:
                                cse_1 = 1.0
                            else:
                                cse_1 = 0.0
                            if (not(cse_2)):
                                cse_4 = 1.0
                            else:
                                cse_4 = (1.0 - cse_1)
                            cse_3 = isclose(cse_4, 0.0)
                            if (not(isclose(cse_1, 0.0))):
                                l_165_impA = (not(cse_2))
                            else:
                                l_165_impA = True
                            if (not(cse_3)):
                                l_166_impB = (cse_4 == 0.0)
                            else:
                                l_166_impB = True
                            _s3 = [True, False]
                            _s4 = []
                            for _v5 in _s3:
                                cse_6 = (sample[1] == EmptyInferenceList())
                                cse_5 = ((not(cse_6)) and (not(cse_6)))
                                if (not(isclose(cse_1, 0.0))):
                                    l_161_pA = (cse_1 * (9.999999999999998e-2 if (not(_v5)) else 0.9))
                                else:
                                    l_161_pA = 0.0
                                if (not(cse_3)):
                                    l_162_pB = (cse_4 * (0.8 if (not(_v5)) else 0.2))
                                else:
                                    l_162_pB = 0.0
                                if (not(cse_6)):
                                    if isAny(sample[1][0]):
                                        l_320_any_shared_0 = 1.0
                                        l_320_any_shared_1 = False
                                        l_320_any_shared = T(l_320_any_shared_0, l_320_any_shared_1)
                                    else:
                                        if (not(cse_2)):
                                            cse_8 = 1.0
                                        else:
                                            cse_8 = (1.0 - cse_1)
                                        cse_7 = isclose(cse_8, 0.0)
                                        if (not(isclose(cse_1, 0.0))):
                                            l_317_impA = (not(cse_2))
                                        else:
                                            l_317_impA = True
                                        if (not(cse_7)):
                                            l_318_impB = (cse_8 == 0.0)
                                        else:
                                            l_318_impB = True
                                        l_319_enum_mass = sum([((l_313_pA:=((cse_1 * (9.999999999999998e-2 if (not(h0)) else 0.9)) if (not(isclose(cse_1, 0.0))) else 0.0)), ((l_314_pB:=((cse_8 * (0.8 if (not(h0)) else 0.2)) if (not(cse_7)) else 0.0)), T((((1.0 if (False == _v5) else 0.0) if (not(h0)) else 0.0) * (l_314_pB if l_317_impA else (l_313_pA if l_318_impB else (l_313_pA + l_314_pB)))), T(0, T(1.0, False))))[1])[1][0] for h0 in [True, False]])
                                        if sample[1][0]:
                                            l_320_any_shared_0 = 1.0
                                            l_320_any_shared_1 = False
                                            l_320_any_shared = T(l_320_any_shared_0, l_320_any_shared_1)
                                        else:
                                            l_320_any_shared_0 = l_319_enum_mass
                                            l_320_any_shared_1 = (l_319_enum_mass == 0.0)
                                            l_320_any_shared = T(l_320_any_shared_0, l_320_any_shared_1)
                                    l_321_guarded_0 = l_320_any_shared[0]
                                    l_321_guarded_1_0 = 0
                                    l_321_guarded_1_1_0 = 0.0
                                    l_321_guarded_1_1_1 = l_320_any_shared[1]
                                    l_321_guarded_1_1 = T(l_321_guarded_1_1_0, l_321_guarded_1_1_1)
                                    l_321_guarded_1 = T(l_321_guarded_1_0, l_321_guarded_1_1)
                                    l_321_guarded = T(l_321_guarded_0, l_321_guarded_1)
                                else:
                                    l_321_guarded_0 = 0.0
                                    l_321_guarded_1_0 = 0
                                    l_321_guarded_1_1_0 = 0.0
                                    l_321_guarded_1_1_1 = True
                                    l_321_guarded_1_1 = T(l_321_guarded_1_1_0, l_321_guarded_1_1_1)
                                    l_321_guarded_1 = T(l_321_guarded_1_0, l_321_guarded_1_1)
                                    l_321_guarded = T(l_321_guarded_0, l_321_guarded_1)
                                if (not(cse_6)):
                                    if (not(l_321_guarded[1][1][1])):
                                        if isAny(sample[1][1:]):
                                            l_1263_any_shared_0 = 1.0
                                            l_1263_any_shared_1 = False
                                            l_1263_any_shared = T(l_1263_any_shared_0, l_1263_any_shared_1)
                                        else:
                                            if (not(cse_2)):
                                                cse_10 = 1.0
                                            else:
                                                cse_10 = (1.0 - cse_1)
                                            cse_9 = isclose(cse_10, 0.0)
                                            if (not(isclose(cse_1, 0.0))):
                                                l_338_impA = (not(cse_2))
                                            else:
                                                l_338_impA = True
                                            if (not(cse_9)):
                                                l_339_impB = (cse_10 == 0.0)
                                            else:
                                                l_339_impB = True
                                            l_1262_enum_mass = sum([((cse_12:=(sample[1][1:] == EmptyInferenceList())), ((cse_11:=((not(cse_12)) and (not(cse_12)))), ((l_334_pA:=((cse_1 * (9.999999999999998e-2 if (not(h2)) else 0.9)) if (not(isclose(cse_1, 0.0))) else 0.0)), ((l_335_pB:=((cse_10 * (0.8 if (not(h2)) else 0.2)) if (not(cse_9)) else 0.0)), ((l_1260_guarded:=((((l_1259_any_shared:=(T(1.0, False) if isAny(sample[1][1:][1:]) else ((cse_15:=(1.0 if (not(cse_2)) else (1.0 - cse_1))), ((cse_14:=isclose(cse_15, 0.0)), ((l_484_impA:=((not(cse_2)) if (not(isclose(cse_1, 0.0))) else True)), ((l_485_impB:=((cse_15 == 0.0) if (not(cse_14)) else True)), ((l_1258_enum_mass:=sum([((cse_17:=(sample[1][1:][1:] == EmptyInferenceList())), ((cse_16:=((not(cse_17)) and (not(cse_17)))), ((l_480_pA:=((cse_1 * (9.999999999999998e-2 if (not(h3)) else 0.9)) if (not(isclose(cse_1, 0.0))) else 0.0)), ((l_481_pB:=((cse_15 * (0.8 if (not(h3)) else 0.2)) if (not(cse_14)) else 0.0)), ((l_1256_guarded:=((((l_1255_any_shared:=(T(1.0, False) if isAny(sample[1][1:][1:][1:]) else ((cse_20:=(1.0 if (not(cse_2)) else (1.0 - cse_1))), ((cse_19:=isclose(cse_20, 0.0)), ((l_618_impA:=((not(cse_2)) if (not(isclose(cse_1, 0.0))) else True)), ((l_619_impB:=((cse_20 == 0.0) if (not(cse_19)) else True)), ((l_1254_enum_mass:=sum([((cse_22:=(sample[1][1:][1:][1:] == EmptyInferenceList())), ((cse_21:=((not(cse_22)) and (not(cse_22)))), ((l_614_pA:=((cse_1 * (9.999999999999998e-2 if (not(h4)) else 0.9)) if (not(isclose(cse_1, 0.0))) else 0.0)), ((l_615_pB:=((cse_20 * (0.8 if (not(h4)) else 0.2)) if (not(cse_19)) else 0.0)), ((l_1252_guarded:=((((l_1251_any_shared:=(T(1.0, False) if isAny(sample[1][1:][1:][1:][1:]) else ((cse_25:=(1.0 if (not(cse_2)) else (1.0 - cse_1))), ((cse_24:=isclose(cse_25, 0.0)), ((l_740_impA:=((not(cse_2)) if (not(isclose(cse_1, 0.0))) else True)), ((l_741_impB:=((cse_25 == 0.0) if (not(cse_24)) else True)), ((l_1250_enum_mass:=sum([((cse_27:=(sample[1][1:][1:][1:][1:] == EmptyInferenceList())), ((cse_26:=((not(cse_27)) and (not(cse_27)))), ((l_736_pA:=((cse_1 * (9.999999999999998e-2 if (not(h5)) else 0.9)) if (not(isclose(cse_1, 0.0))) else 0.0)), ((l_737_pB:=((cse_25 * (0.8 if (not(h5)) else 0.2)) if (not(cse_24)) else 0.0)), ((l_1248_guarded:=((((l_1247_any_shared:=(T(1.0, False) if isAny(sample[1][1:][1:][1:][1:][1:]) else ((cse_30:=(1.0 if (not(cse_2)) else (1.0 - cse_1))), ((cse_29:=isclose(cse_30, 0.0)), ((l_850_impA:=((not(cse_2)) if (not(isclose(cse_1, 0.0))) else True)), ((l_851_impB:=((cse_30 == 0.0) if (not(cse_29)) else True)), ((l_1246_enum_mass:=sum([((cse_32:=(sample[1][1:][1:][1:][1:][1:] == EmptyInferenceList())), ((cse_31:=((not(cse_32)) and (not(cse_32)))), ((l_846_pA:=((cse_1 * (9.999999999999998e-2 if (not(h6)) else 0.9)) if (not(isclose(cse_1, 0.0))) else 0.0)), ((l_847_pB:=((cse_30 * (0.8 if (not(h6)) else 0.2)) if (not(cse_29)) else 0.0)), ((l_1244_guarded:=((((l_1243_any_shared:=(T(1.0, False) if isAny(sample[1][1:][1:][1:][1:][1:][1:]) else ((cse_35:=(1.0 if (not(cse_2)) else (1.0 - cse_1))), ((cse_34:=isclose(cse_35, 0.0)), ((l_948_impA:=((not(cse_2)) if (not(isclose(cse_1, 0.0))) else True)), ((l_949_impB:=((cse_35 == 0.0) if (not(cse_34)) else True)), ((l_1242_enum_mass:=sum([((cse_37:=(sample[1][1:][1:][1:][1:][1:][1:] == EmptyInferenceList())), ((cse_36:=((not(cse_37)) and (not(cse_37)))), ((l_944_pA:=((cse_1 * (9.999999999999998e-2 if (not(h7)) else 0.9)) if (not(isclose(cse_1, 0.0))) else 0.0)), ((l_945_pB:=((cse_35 * (0.8 if (not(h7)) else 0.2)) if (not(cse_34)) else 0.0)), ((l_1240_guarded:=((((l_1239_any_shared:=(T(1.0, False) if isAny(sample[1][1:][1:][1:][1:][1:][1:][1:]) else ((cse_40:=(1.0 if (not(cse_2)) else (1.0 - cse_1))), ((cse_39:=isclose(cse_40, 0.0)), ((l_1034_impA:=((not(cse_2)) if (not(isclose(cse_1, 0.0))) else True)), ((l_1035_impB:=((cse_40 == 0.0) if (not(cse_39)) else True)), ((l_1238_enum_mass:=sum([((cse_42:=(sample[1][1:][1:][1:][1:][1:][1:][1:] == EmptyInferenceList())), ((cse_41:=((not(cse_42)) and (not(cse_42)))), ((l_1030_pA:=((cse_1 * (9.999999999999998e-2 if (not(h8)) else 0.9)) if (not(isclose(cse_1, 0.0))) else 0.0)), ((l_1031_pB:=((cse_40 * (0.8 if (not(h8)) else 0.2)) if (not(cse_39)) else 0.0)), ((l_1236_guarded:=((((l_1235_any_shared:=(T(1.0, False) if isAny(sample[1][1:][1:][1:][1:][1:][1:][1:][1:]) else ((cse_45:=(1.0 if (not(cse_2)) else (1.0 - cse_1))), ((cse_44:=isclose(cse_45, 0.0)), ((l_1108_impA:=((not(cse_2)) if (not(isclose(cse_1, 0.0))) else True)), ((l_1109_impB:=((cse_45 == 0.0) if (not(cse_44)) else True)), ((l_1234_enum_mass:=sum([((cse_47:=(sample[1][1:][1:][1:][1:][1:][1:][1:][1:] == EmptyInferenceList())), ((cse_46:=((not(cse_47)) and (not(cse_47)))), ((l_1104_pA:=((cse_1 * (9.999999999999998e-2 if (not(h9)) else 0.9)) if (not(isclose(cse_1, 0.0))) else 0.0)), ((l_1105_pB:=((cse_45 * (0.8 if (not(h9)) else 0.2)) if (not(cse_44)) else 0.0)), ((l_1232_guarded:=((((l_1231_any_shared:=(T(1.0, False) if isAny(sample[1][1:][1:][1:][1:][1:][1:][1:][1:][1:]) else ((cse_50:=(1.0 if (not(cse_2)) else (1.0 - cse_1))), ((cse_49:=isclose(cse_50, 0.0)), ((l_1170_impA:=((not(cse_2)) if (not(isclose(cse_1, 0.0))) else True)), ((l_1171_impB:=((cse_50 == 0.0) if (not(cse_49)) else True)), ((l_1230_enum_mass:=sum([((cse_52:=(sample[1][1:][1:][1:][1:][1:][1:][1:][1:][1:] == EmptyInferenceList())), ((cse_51:=((not(cse_52)) and (not(cse_52)))), ((l_1166_pA:=((cse_1 * (9.999999999999998e-2 if (not(h10)) else 0.9)) if (not(isclose(cse_1, 0.0))) else 0.0)), ((l_1167_pB:=((cse_50 * (0.8 if (not(h10)) else 0.2)) if (not(cse_49)) else 0.0)), ((l_1228_guarded:=((((l_1227_any_shared:=(T(1.0, False) if isAny(sample[1][1:][1:][1:][1:][1:][1:][1:][1:][1:][1:]) else ((cse_55:=(1.0 if (not(cse_2)) else (1.0 - cse_1))), ((cse_54:=isclose(cse_55, 0.0)), ((l_1220_impA:=((not(cse_2)) if (not(isclose(cse_1, 0.0))) else True)), ((l_1221_impB:=((cse_55 == 0.0) if (not(cse_54)) else True)), ((l_1226_enum_mass:=sum([((l_1216_pA:=((cse_1 * (9.999999999999998e-2 if (not(h11)) else 0.9)) if (not(isclose(cse_1, 0.0))) else 0.0)), ((l_1217_pB:=((cse_55 * (0.8 if (not(h11)) else 0.2)) if (not(cse_54)) else 0.0)), T(((l_1217_pB if l_1220_impA else (l_1216_pA if l_1221_impB else (l_1216_pA + l_1217_pB))) if (sample[1][1:][1:][1:][1:][1:][1:][1:][1:][1:][1:] == ConsInferenceList((True if h10 else h11), EmptyInferenceList())) else 0.0), T(0, T(1.0, False))))[1])[1][0] for h11 in [True, False]])), T(l_1226_enum_mass, (l_1226_enum_mass == 0.0)))[1])[1])[1])[1])[1])), T(l_1227_any_shared[0], T(0, T(0.0, l_1227_any_shared[1]))))[1] if (not((False if isAny(sample[1][1:][1:][1:][1:][1:][1:][1:][1:][1:][0]) else ((cse_53:=(True if isAny(h9) else (True == h9))), ((l_1194_pB:=(1.0 if cse_53 else 0.0)), ((l_1197_impB:=(not(cse_53))), (False if sample[1][1:][1:][1:][1:][1:][1:][1:][1:][1:][0] else ((((not(cse_53)) or (not((True if isAny(h10) else (False == h10))))) if (not(isclose((1.0 if cse_53 else 0.0), 0.0))) else True) and (((1.0 if l_1197_impB else (1.0 - l_1194_pB)) == 0.0) if (not(isclose((1.0 if l_1197_impB else (1.0 - l_1194_pB)), 0.0))) else True))))[1])[1])[1]))) else T(0.0, T(0, T(0.0, True)))) if (not(cse_52)) else T(0.0, T(0, T(0.0, True))))), T((((((1.0 if isAny(sample[1][1:][1:][1:][1:][1:][1:][1:][1:][1:][0]) else ((cse_57:=(True if isAny(h9) else (True == h9))), ((cse_56:=(1.0 if cse_57 else 0.0)), ((l_1197_impB:=(not(cse_57))), ((cse_58:=isclose((1.0 if l_1197_impB else (1.0 - cse_56)), 0.0)), ((l_1198_pA:=((cse_56 if (True if isAny(h10) else (False == h10)) else 0.0) if (not(isclose(cse_56, 0.0))) else 0.0)), ((l_1199_pB:=((1.0 if l_1197_impB else (1.0 - cse_56)) if (not(cse_58)) else 0.0)), (1.0 if sample[1][1:][1:][1:][1:][1:][1:][1:][1:][1:][0] else (l_1199_pB if (((not(cse_57)) or (not((True if isAny(h10) else (False == h10))))) if (not(isclose(cse_56, 0.0))) else True) else (l_1198_pA if (((1.0 if l_1197_impB else (1.0 - cse_56)) == 0.0) if (not(cse_58)) else True) else (l_1198_pA + l_1199_pB)))))[1])[1])[1])[1])[1])[1]) if (not(cse_52)) else 0.0) * l_1228_guarded[0]) if cse_51 else 0.0) * (l_1167_pB if l_1170_impA else (l_1166_pA if l_1171_impB else (l_1166_pA + l_1167_pB)))), T(0, (T((0.0 if isAny(sample[1][1:][1:][1:][1:][1:][1:][1:][1:][1:][0]) else ((cse_60:=(True if isAny(h9) else (True == h9))), ((cse_59:=(1.0 if cse_60 else 0.0)), ((0.0 if isclose(cse_59, 0.0) else 1.0) + (0.0 if isclose((1.0 if (not(cse_60)) else (1.0 - cse_59)), 0.0) else 1.0)))[1])[1]), (((False if isAny(sample[1][1:][1:][1:][1:][1:][1:][1:][1:][1:][0]) else ((cse_61:=(True if isAny(h9) else (True == h9))), ((l_1194_pB:=(1.0 if cse_61 else 0.0)), ((l_1197_impB:=(not(cse_61))), (False if sample[1][1:][1:][1:][1:][1:][1:][1:][1:][1:][0] else ((((not(cse_61)) or (not((True if isAny(h10) else (False == h10))))) if (not(isclose((1.0 if cse_61 else 0.0), 0.0))) else True) and (((1.0 if l_1197_impB else (1.0 - l_1194_pB)) == 0.0) if (not(isclose((1.0 if l_1197_impB else (1.0 - l_1194_pB)), 0.0))) else True))))[1])[1])[1]) if (not(cse_52)) else True) or l_1228_guarded[1][1][1])) if cse_51 else T(0.0, True)))))[1])[1])[1][0])[1])[1] for h10 in [True, False]])), T(l_1230_enum_mass, (l_1230_enum_mass == 0.0)))[1])[1])[1])[1])[1])), T(l_1231_any_shared[0], T(0, T(0.0, l_1231_any_shared[1]))))[1] if (not((False if isAny(sample[1][1:][1:][1:][1:][1:][1:][1:][1:][0]) else ((cse_48:=(True if isAny(h8) else (True == h8))), ((l_1144_pB:=(1.0 if cse_48 else 0.0)), ((l_1147_impB:=(not(cse_48))), (False if sample[1][1:][1:][1:][1:][1:][1:][1:][1:][0] else ((((1.0 if l_1147_impB else (1.0 - l_1144_pB)) == 0.0) or (not((True if isAny(h9) else (False == h9))))) if (not(isclose((1.0 if l_1147_impB else (1.0 - l_1144_pB)), 0.0))) else True)))[1])[1])[1]))) else T(0.0, T(0, T(0.0, True)))) if (not(cse_47)) else T(0.0, T(0, T(0.0, True))))), T((((((1.0 if isAny(sample[1][1:][1:][1:][1:][1:][1:][1:][1:][0]) else ((cse_62:=(True if isAny(h8) else (True == h8))), ((l_1144_pB:=(1.0 if cse_62 else 0.0)), ((l_1147_impB:=(not(cse_62))), (1.0 if sample[1][1:][1:][1:][1:][1:][1:][1:][1:][0] else (((1.0 if l_1147_impB else (1.0 - l_1144_pB)) if (True if isAny(h9) else (False == h9)) else 0.0) if (not(isclose((1.0 if l_1147_impB else (1.0 - l_1144_pB)), 0.0))) else 0.0)))[1])[1])[1]) if (not(cse_47)) else 0.0) * l_1232_guarded[0]) if cse_46 else 0.0) * (l_1105_pB if l_1108_impA else (l_1104_pA if l_1109_impB else (l_1104_pA + l_1105_pB)))), T(0, (T((0.0 if isAny(sample[1][1:][1:][1:][1:][1:][1:][1:][1:][0]) else ((cse_65:=(True if isAny(h8) else (True == h8))), ((cse_64:=(1.0 if cse_65 else 0.0)), ((0.0 if isclose(cse_64, 0.0) else 1.0) + (0.0 if isclose((1.0 if (not(cse_65)) else (1.0 - cse_64)), 0.0) else 1.0)))[1])[1]), (((False if isAny(sample[1][1:][1:][1:][1:][1:][1:][1:][1:][0]) else ((cse_66:=(True if isAny(h8) else (True == h8))), ((l_1144_pB:=(1.0 if cse_66 else 0.0)), ((l_1147_impB:=(not(cse_66))), (False if sample[1][1:][1:][1:][1:][1:][1:][1:][1:][0] else ((((1.0 if l_1147_impB else (1.0 - l_1144_pB)) == 0.0) or (not((True if isAny(h9) else (False == h9))))) if (not(isclose((1.0 if l_1147_impB else (1.0 - l_1144_pB)), 0.0))) else True)))[1])[1])[1]) if (not(cse_47)) else True) or l_1232_guarded[1][1][1])) if cse_46 else T(0.0, True)))))[1])[1])[1][0])[1])[1] for h9 in [True, False]])), T(l_1234_enum_mass, (l_1234_enum_mass == 0.0)))[1])[1])[1])[1])[1])), T(l_1235_any_shared[0], T(0, T(0.0, l_1235_any_shared[1]))))[1] if (not((False if isAny(sample[1][1:][1:][1:][1:][1:][1:][1:][0]) else ((cse_43:=(True if isAny(h7) else (True == h7))), ((l_1082_pB:=(1.0 if cse_43 else 0.0)), ((l_1085_impB:=(not(cse_43))), (False if sample[1][1:][1:][1:][1:][1:][1:][1:][0] else ((((not(cse_43)) or (not((True if isAny(h8) else (False == h8))))) if (not(isclose((1.0 if cse_43 else 0.0), 0.0))) else True) and (((1.0 if l_1085_impB else (1.0 - l_1082_pB)) == 0.0) if (not(isclose((1.0 if l_1085_impB else (1.0 - l_1082_pB)), 0.0))) else True))))[1])[1])[1]))) else T(0.0, T(0, T(0.0, True)))) if (not(cse_42)) else T(0.0, T(0, T(0.0, True))))), T((((((1.0 if isAny(sample[1][1:][1:][1:][1:][1:][1:][1:][0]) else ((cse_68:=(True if isAny(h7) else (True == h7))), ((cse_67:=(1.0 if cse_68 else 0.0)), ((l_1085_impB:=(not(cse_68))), ((cse_69:=isclose((1.0 if l_1085_impB else (1.0 - cse_67)), 0.0)), ((l_1086_pA:=((cse_67 if (True if isAny(h8) else (False == h8)) else 0.0) if (not(isclose(cse_67, 0.0))) else 0.0)), ((l_1087_pB:=((1.0 if l_1085_impB else (1.0 - cse_67)) if (not(cse_69)) else 0.0)), (1.0 if sample[1][1:][1:][1:][1:][1:][1:][1:][0] else (l_1087_pB if (((not(cse_68)) or (not((True if isAny(h8) else (False == h8))))) if (not(isclose(cse_67, 0.0))) else True) else (l_1086_pA if (((1.0 if l_1085_impB else (1.0 - cse_67)) == 0.0) if (not(cse_69)) else True) else (l_1086_pA + l_1087_pB)))))[1])[1])[1])[1])[1])[1]) if (not(cse_42)) else 0.0) * l_1236_guarded[0]) if cse_41 else 0.0) * (l_1031_pB if l_1034_impA else (l_1030_pA if l_1035_impB else (l_1030_pA + l_1031_pB)))), T(0, (T((0.0 if isAny(sample[1][1:][1:][1:][1:][1:][1:][1:][0]) else ((cse_71:=(True if isAny(h7) else (True == h7))), ((cse_70:=(1.0 if cse_71 else 0.0)), ((0.0 if isclose(cse_70, 0.0) else 1.0) + (0.0 if isclose((1.0 if (not(cse_71)) else (1.0 - cse_70)), 0.0) else 1.0)))[1])[1]), (((False if isAny(sample[1][1:][1:][1:][1:][1:][1:][1:][0]) else ((cse_72:=(True if isAny(h7) else (True == h7))), ((l_1082_pB:=(1.0 if cse_72 else 0.0)), ((l_1085_impB:=(not(cse_72))), (False if sample[1][1:][1:][1:][1:][1:][1:][1:][0] else ((((not(cse_72)) or (not((True if isAny(h8) else (False == h8))))) if (not(isclose((1.0 if cse_72 else 0.0), 0.0))) else True) and (((1.0 if l_1085_impB else (1.0 - l_1082_pB)) == 0.0) if (not(isclose((1.0 if l_1085_impB else (1.0 - l_1082_pB)), 0.0))) else True))))[1])[1])[1]) if (not(cse_42)) else True) or l_1236_guarded[1][1][1])) if cse_41 else T(0.0, True)))))[1])[1])[1][0])[1])[1] for h8 in [True, False]])), T(l_1238_enum_mass, (l_1238_enum_mass == 0.0)))[1])[1])[1])[1])[1])), T(l_1239_any_shared[0], T(0, T(0.0, l_1239_any_shared[1]))))[1] if (not((False if isAny(sample[1][1:][1:][1:][1:][1:][1:][0]) else ((cse_38:=(True if isAny(h6) else (True == h6))), ((l_1008_pB:=(1.0 if cse_38 else 0.0)), ((l_1011_impB:=(not(cse_38))), (False if sample[1][1:][1:][1:][1:][1:][1:][0] else ((((1.0 if l_1011_impB else (1.0 - l_1008_pB)) == 0.0) or (not((True if isAny(h7) else (False == h7))))) if (not(isclose((1.0 if l_1011_impB else (1.0 - l_1008_pB)), 0.0))) else True)))[1])[1])[1]))) else T(0.0, T(0, T(0.0, True)))) if (not(cse_37)) else T(0.0, T(0, T(0.0, True))))), T((((((1.0 if isAny(sample[1][1:][1:][1:][1:][1:][1:][0]) else ((cse_73:=(True if isAny(h6) else (True == h6))), ((l_1008_pB:=(1.0 if cse_73 else 0.0)), ((l_1011_impB:=(not(cse_73))), (1.0 if sample[1][1:][1:][1:][1:][1:][1:][0] else (((1.0 if l_1011_impB else (1.0 - l_1008_pB)) if (True if isAny(h7) else (False == h7)) else 0.0) if (not(isclose((1.0 if l_1011_impB else (1.0 - l_1008_pB)), 0.0))) else 0.0)))[1])[1])[1]) if (not(cse_37)) else 0.0) * l_1240_guarded[0]) if cse_36 else 0.0) * (l_945_pB if l_948_impA else (l_944_pA if l_949_impB else (l_944_pA + l_945_pB)))), T(0, (T((0.0 if isAny(sample[1][1:][1:][1:][1:][1:][1:][0]) else ((cse_76:=(True if isAny(h6) else (True == h6))), ((cse_75:=(1.0 if cse_76 else 0.0)), ((0.0 if isclose(cse_75, 0.0) else 1.0) + (0.0 if isclose((1.0 if (not(cse_76)) else (1.0 - cse_75)), 0.0) else 1.0)))[1])[1]), (((False if isAny(sample[1][1:][1:][1:][1:][1:][1:][0]) else ((cse_77:=(True if isAny(h6) else (True == h6))), ((l_1008_pB:=(1.0 if cse_77 else 0.0)), ((l_1011_impB:=(not(cse_77))), (False if sample[1][1:][1:][1:][1:][1:][1:][0] else ((((1.0 if l_1011_impB else (1.0 - l_1008_pB)) == 0.0) or (not((True if isAny(h7) else (False == h7))))) if (not(isclose((1.0 if l_1011_impB else (1.0 - l_1008_pB)), 0.0))) else True)))[1])[1])[1]) if (not(cse_37)) else True) or l_1240_guarded[1][1][1])) if cse_36 else T(0.0, True)))))[1])[1])[1][0])[1])[1] for h7 in [True, False]])), T(l_1242_enum_mass, (l_1242_enum_mass == 0.0)))[1])[1])[1])[1])[1])), T(l_1243_any_shared[0], T(0, T(0.0, l_1243_any_shared[1]))))[1] if (not((False if isAny(sample[1][1:][1:][1:][1:][1:][0]) else ((cse_33:=(True if isAny(h5) else (True == h5))), ((l_922_pB:=(1.0 if cse_33 else 0.0)), ((l_925_impB:=(not(cse_33))), (False if sample[1][1:][1:][1:][1:][1:][0] else ((((not(cse_33)) or (not((True if isAny(h6) else (False == h6))))) if (not(isclose((1.0 if cse_33 else 0.0), 0.0))) else True) and (((1.0 if l_925_impB else (1.0 - l_922_pB)) == 0.0) if (not(isclose((1.0 if l_925_impB else (1.0 - l_922_pB)), 0.0))) else True))))[1])[1])[1]))) else T(0.0, T(0, T(0.0, True)))) if (not(cse_32)) else T(0.0, T(0, T(0.0, True))))), T((((((1.0 if isAny(sample[1][1:][1:][1:][1:][1:][0]) else ((cse_79:=(True if isAny(h5) else (True == h5))), ((cse_78:=(1.0 if cse_79 else 0.0)), ((l_925_impB:=(not(cse_79))), ((cse_80:=isclose((1.0 if l_925_impB else (1.0 - cse_78)), 0.0)), ((l_926_pA:=((cse_78 if (True if isAny(h6) else (False == h6)) else 0.0) if (not(isclose(cse_78, 0.0))) else 0.0)), ((l_927_pB:=((1.0 if l_925_impB else (1.0 - cse_78)) if (not(cse_80)) else 0.0)), (1.0 if sample[1][1:][1:][1:][1:][1:][0] else (l_927_pB if (((not(cse_79)) or (not((True if isAny(h6) else (False == h6))))) if (not(isclose(cse_78, 0.0))) else True) else (l_926_pA if (((1.0 if l_925_impB else (1.0 - cse_78)) == 0.0) if (not(cse_80)) else True) else (l_926_pA + l_927_pB)))))[1])[1])[1])[1])[1])[1]) if (not(cse_32)) else 0.0) * l_1244_guarded[0]) if cse_31 else 0.0) * (l_847_pB if l_850_impA else (l_846_pA if l_851_impB else (l_846_pA + l_847_pB)))), T(0, (T((0.0 if isAny(sample[1][1:][1:][1:][1:][1:][0]) else ((cse_82:=(True if isAny(h5) else (True == h5))), ((cse_81:=(1.0 if cse_82 else 0.0)), ((0.0 if isclose(cse_81, 0.0) else 1.0) + (0.0 if isclose((1.0 if (not(cse_82)) else (1.0 - cse_81)), 0.0) else 1.0)))[1])[1]), (((False if isAny(sample[1][1:][1:][1:][1:][1:][0]) else ((cse_83:=(True if isAny(h5) else (True == h5))), ((l_922_pB:=(1.0 if cse_83 else 0.0)), ((l_925_impB:=(not(cse_83))), (False if sample[1][1:][1:][1:][1:][1:][0] else ((((not(cse_83)) or (not((True if isAny(h6) else (False == h6))))) if (not(isclose((1.0 if cse_83 else 0.0), 0.0))) else True) and (((1.0 if l_925_impB else (1.0 - l_922_pB)) == 0.0) if (not(isclose((1.0 if l_925_impB else (1.0 - l_922_pB)), 0.0))) else True))))[1])[1])[1]) if (not(cse_32)) else True) or l_1244_guarded[1][1][1])) if cse_31 else T(0.0, True)))))[1])[1])[1][0])[1])[1] for h6 in [True, False]])), T(l_1246_enum_mass, (l_1246_enum_mass == 0.0)))[1])[1])[1])[1])[1])), T(l_1247_any_shared[0], T(0, T(0.0, l_1247_any_shared[1]))))[1] if (not((False if isAny(sample[1][1:][1:][1:][1:][0]) else ((cse_28:=(True if isAny(h4) else (True == h4))), ((l_824_pB:=(1.0 if cse_28 else 0.0)), ((l_827_impB:=(not(cse_28))), (False if sample[1][1:][1:][1:][1:][0] else ((((1.0 if l_827_impB else (1.0 - l_824_pB)) == 0.0) or (not((True if isAny(h5) else (False == h5))))) if (not(isclose((1.0 if l_827_impB else (1.0 - l_824_pB)), 0.0))) else True)))[1])[1])[1]))) else T(0.0, T(0, T(0.0, True)))) if (not(cse_27)) else T(0.0, T(0, T(0.0, True))))), T((((((1.0 if isAny(sample[1][1:][1:][1:][1:][0]) else ((cse_84:=(True if isAny(h4) else (True == h4))), ((l_824_pB:=(1.0 if cse_84 else 0.0)), ((l_827_impB:=(not(cse_84))), (1.0 if sample[1][1:][1:][1:][1:][0] else (((1.0 if l_827_impB else (1.0 - l_824_pB)) if (True if isAny(h5) else (False == h5)) else 0.0) if (not(isclose((1.0 if l_827_impB else (1.0 - l_824_pB)), 0.0))) else 0.0)))[1])[1])[1]) if (not(cse_27)) else 0.0) * l_1248_guarded[0]) if cse_26 else 0.0) * (l_737_pB if l_740_impA else (l_736_pA if l_741_impB else (l_736_pA + l_737_pB)))), T(0, (T((0.0 if isAny(sample[1][1:][1:][1:][1:][0]) else ((cse_87:=(True if isAny(h4) else (True == h4))), ((cse_86:=(1.0 if cse_87 else 0.0)), ((0.0 if isclose(cse_86, 0.0) else 1.0) + (0.0 if isclose((1.0 if (not(cse_87)) else (1.0 - cse_86)), 0.0) else 1.0)))[1])[1]), (((False if isAny(sample[1][1:][1:][1:][1:][0]) else ((cse_88:=(True if isAny(h4) else (True == h4))), ((l_824_pB:=(1.0 if cse_88 else 0.0)), ((l_827_impB:=(not(cse_88))), (False if sample[1][1:][1:][1:][1:][0] else ((((1.0 if l_827_impB else (1.0 - l_824_pB)) == 0.0) or (not((True if isAny(h5) else (False == h5))))) if (not(isclose((1.0 if l_827_impB else (1.0 - l_824_pB)), 0.0))) else True)))[1])[1])[1]) if (not(cse_27)) else True) or l_1248_guarded[1][1][1])) if cse_26 else T(0.0, True)))))[1])[1])[1][0])[1])[1] for h5 in [True, False]])), T(l_1250_enum_mass, (l_1250_enum_mass == 0.0)))[1])[1])[1])[1])[1])), T(l_1251_any_shared[0], T(0, T(0.0, l_1251_any_shared[1]))))[1] if (not((False if isAny(sample[1][1:][1:][1:][0]) else ((cse_23:=(True if isAny(h3) else (True == h3))), ((l_714_pB:=(1.0 if cse_23 else 0.0)), ((l_717_impB:=(not(cse_23))), (False if sample[1][1:][1:][1:][0] else ((((not(cse_23)) or (not((True if isAny(h4) else (False == h4))))) if (not(isclose((1.0 if cse_23 else 0.0), 0.0))) else True) and (((1.0 if l_717_impB else (1.0 - l_714_pB)) == 0.0) if (not(isclose((1.0 if l_717_impB else (1.0 - l_714_pB)), 0.0))) else True))))[1])[1])[1]))) else T(0.0, T(0, T(0.0, True)))) if (not(cse_22)) else T(0.0, T(0, T(0.0, True))))), T((((((1.0 if isAny(sample[1][1:][1:][1:][0]) else ((cse_90:=(True if isAny(h3) else (True == h3))), ((cse_89:=(1.0 if cse_90 else 0.0)), ((l_717_impB:=(not(cse_90))), ((cse_91:=isclose((1.0 if l_717_impB else (1.0 - cse_89)), 0.0)), ((l_718_pA:=((cse_89 if (True if isAny(h4) else (False == h4)) else 0.0) if (not(isclose(cse_89, 0.0))) else 0.0)), ((l_719_pB:=((1.0 if l_717_impB else (1.0 - cse_89)) if (not(cse_91)) else 0.0)), (1.0 if sample[1][1:][1:][1:][0] else (l_719_pB if (((not(cse_90)) or (not((True if isAny(h4) else (False == h4))))) if (not(isclose(cse_89, 0.0))) else True) else (l_718_pA if (((1.0 if l_717_impB else (1.0 - cse_89)) == 0.0) if (not(cse_91)) else True) else (l_718_pA + l_719_pB)))))[1])[1])[1])[1])[1])[1]) if (not(cse_22)) else 0.0) * l_1252_guarded[0]) if cse_21 else 0.0) * (l_615_pB if l_618_impA else (l_614_pA if l_619_impB else (l_614_pA + l_615_pB)))), T(0, (T((0.0 if isAny(sample[1][1:][1:][1:][0]) else ((cse_93:=(True if isAny(h3) else (True == h3))), ((cse_92:=(1.0 if cse_93 else 0.0)), ((0.0 if isclose(cse_92, 0.0) else 1.0) + (0.0 if isclose((1.0 if (not(cse_93)) else (1.0 - cse_92)), 0.0) else 1.0)))[1])[1]), (((False if isAny(sample[1][1:][1:][1:][0]) else ((cse_94:=(True if isAny(h3) else (True == h3))), ((l_714_pB:=(1.0 if cse_94 else 0.0)), ((l_717_impB:=(not(cse_94))), (False if sample[1][1:][1:][1:][0] else ((((not(cse_94)) or (not((True if isAny(h4) else (False == h4))))) if (not(isclose((1.0 if cse_94 else 0.0), 0.0))) else True) and (((1.0 if l_717_impB else (1.0 - l_714_pB)) == 0.0) if (not(isclose((1.0 if l_717_impB else (1.0 - l_714_pB)), 0.0))) else True))))[1])[1])[1]) if (not(cse_22)) else True) or l_1252_guarded[1][1][1])) if cse_21 else T(0.0, True)))))[1])[1])[1][0])[1])[1] for h4 in [True, False]])), T(l_1254_enum_mass, (l_1254_enum_mass == 0.0)))[1])[1])[1])[1])[1])), T(l_1255_any_shared[0], T(0, T(0.0, l_1255_any_shared[1]))))[1] if (not((False if isAny(sample[1][1:][1:][0]) else ((cse_18:=(True if isAny(h2) else (True == h2))), ((l_592_pB:=(1.0 if cse_18 else 0.0)), ((l_595_impB:=(not(cse_18))), (False if sample[1][1:][1:][0] else ((((1.0 if l_595_impB else (1.0 - l_592_pB)) == 0.0) or (not((True if isAny(h3) else (False == h3))))) if (not(isclose((1.0 if l_595_impB else (1.0 - l_592_pB)), 0.0))) else True)))[1])[1])[1]))) else T(0.0, T(0, T(0.0, True)))) if (not(cse_17)) else T(0.0, T(0, T(0.0, True))))), T((((((1.0 if isAny(sample[1][1:][1:][0]) else ((cse_95:=(True if isAny(h2) else (True == h2))), ((l_592_pB:=(1.0 if cse_95 else 0.0)), ((l_595_impB:=(not(cse_95))), (1.0 if sample[1][1:][1:][0] else (((1.0 if l_595_impB else (1.0 - l_592_pB)) if (True if isAny(h3) else (False == h3)) else 0.0) if (not(isclose((1.0 if l_595_impB else (1.0 - l_592_pB)), 0.0))) else 0.0)))[1])[1])[1]) if (not(cse_17)) else 0.0) * l_1256_guarded[0]) if cse_16 else 0.0) * (l_481_pB if l_484_impA else (l_480_pA if l_485_impB else (l_480_pA + l_481_pB)))), T(0, (T((0.0 if isAny(sample[1][1:][1:][0]) else ((cse_98:=(True if isAny(h2) else (True == h2))), ((cse_97:=(1.0 if cse_98 else 0.0)), ((0.0 if isclose(cse_97, 0.0) else 1.0) + (0.0 if isclose((1.0 if (not(cse_98)) else (1.0 - cse_97)), 0.0) else 1.0)))[1])[1]), (((False if isAny(sample[1][1:][1:][0]) else ((cse_99:=(True if isAny(h2) else (True == h2))), ((l_592_pB:=(1.0 if cse_99 else 0.0)), ((l_595_impB:=(not(cse_99))), (False if sample[1][1:][1:][0] else ((((1.0 if l_595_impB else (1.0 - l_592_pB)) == 0.0) or (not((True if isAny(h3) else (False == h3))))) if (not(isclose((1.0 if l_595_impB else (1.0 - l_592_pB)), 0.0))) else True)))[1])[1])[1]) if (not(cse_17)) else True) or l_1256_guarded[1][1][1])) if cse_16 else T(0.0, True)))))[1])[1])[1][0])[1])[1] for h3 in [True, False]])), T(l_1258_enum_mass, (l_1258_enum_mass == 0.0)))[1])[1])[1])[1])[1])), T(l_1259_any_shared[0], T(0, T(0.0, l_1259_any_shared[1]))))[1] if (not((False if isAny(sample[1][1:][0]) else ((cse_13:=(True if isAny(_v5) else (True == _v5))), ((l_458_pB:=(1.0 if cse_13 else 0.0)), ((l_461_impB:=(not(cse_13))), (False if sample[1][1:][0] else ((((not(cse_13)) or (not((True if isAny(h2) else (False == h2))))) if (not(isclose((1.0 if cse_13 else 0.0), 0.0))) else True) and (((1.0 if l_461_impB else (1.0 - l_458_pB)) == 0.0) if (not(isclose((1.0 if l_461_impB else (1.0 - l_458_pB)), 0.0))) else True))))[1])[1])[1]))) else T(0.0, T(0, T(0.0, True)))) if (not(cse_12)) else T(0.0, T(0, T(0.0, True))))), T((((((1.0 if isAny(sample[1][1:][0]) else ((cse_101:=(True if isAny(_v5) else (True == _v5))), ((cse_100:=(1.0 if cse_101 else 0.0)), ((l_461_impB:=(not(cse_101))), ((cse_102:=isclose((1.0 if l_461_impB else (1.0 - cse_100)), 0.0)), ((l_462_pA:=((cse_100 if (True if isAny(h2) else (False == h2)) else 0.0) if (not(isclose(cse_100, 0.0))) else 0.0)), ((l_463_pB:=((1.0 if l_461_impB else (1.0 - cse_100)) if (not(cse_102)) else 0.0)), (1.0 if sample[1][1:][0] else (l_463_pB if (((not(cse_101)) or (not((True if isAny(h2) else (False == h2))))) if (not(isclose(cse_100, 0.0))) else True) else (l_462_pA if (((1.0 if l_461_impB else (1.0 - cse_100)) == 0.0) if (not(cse_102)) else True) else (l_462_pA + l_463_pB)))))[1])[1])[1])[1])[1])[1]) if (not(cse_12)) else 0.0) * l_1260_guarded[0]) if cse_11 else 0.0) * (l_335_pB if l_338_impA else (l_334_pA if l_339_impB else (l_334_pA + l_335_pB)))), T(0, (T((0.0 if isAny(sample[1][1:][0]) else ((cse_104:=(True if isAny(_v5) else (True == _v5))), ((cse_103:=(1.0 if cse_104 else 0.0)), ((0.0 if isclose(cse_103, 0.0) else 1.0) + (0.0 if isclose((1.0 if (not(cse_104)) else (1.0 - cse_103)), 0.0) else 1.0)))[1])[1]), (((False if isAny(sample[1][1:][0]) else ((cse_105:=(True if isAny(_v5) else (True == _v5))), ((l_458_pB:=(1.0 if cse_105 else 0.0)), ((l_461_impB:=(not(cse_105))), (False if sample[1][1:][0] else ((((not(cse_105)) or (not((True if isAny(h2) else (False == h2))))) if (not(isclose((1.0 if cse_105 else 0.0), 0.0))) else True) and (((1.0 if l_461_impB else (1.0 - l_458_pB)) == 0.0) if (not(isclose((1.0 if l_461_impB else (1.0 - l_458_pB)), 0.0))) else True))))[1])[1])[1]) if (not(cse_12)) else True) or l_1260_guarded[1][1][1])) if cse_11 else T(0.0, True)))))[1])[1])[1][0])[1])[1] for h2 in [True, False]])
                                            l_1263_any_shared_0 = l_1262_enum_mass
                                            l_1263_any_shared_1 = (l_1262_enum_mass == 0.0)
                                            l_1263_any_shared = T(l_1263_any_shared_0, l_1263_any_shared_1)
                                        l_1264_guarded_0 = l_1263_any_shared[0]
                                        l_1264_guarded_1_0 = 0
                                        l_1264_guarded_1_1_0 = 0.0
                                        l_1264_guarded_1_1_1 = l_1263_any_shared[1]
                                        l_1264_guarded_1_1 = T(l_1264_guarded_1_1_0, l_1264_guarded_1_1_1)
                                        l_1264_guarded_1 = T(l_1264_guarded_1_0, l_1264_guarded_1_1)
                                        l_1264_guarded = T(l_1264_guarded_0, l_1264_guarded_1)
                                    else:
                                        l_1264_guarded_0 = 0.0
                                        l_1264_guarded_1_0 = 0
                                        l_1264_guarded_1_1_0 = 0.0
                                        l_1264_guarded_1_1_1 = True
                                        l_1264_guarded_1_1 = T(l_1264_guarded_1_1_0, l_1264_guarded_1_1_1)
                                        l_1264_guarded_1 = T(l_1264_guarded_1_0, l_1264_guarded_1_1)
                                        l_1264_guarded = T(l_1264_guarded_0, l_1264_guarded_1)
                                else:
                                    l_1264_guarded_0 = 0.0
                                    l_1264_guarded_1_0 = 0
                                    l_1264_guarded_1_1_0 = 0.0
                                    l_1264_guarded_1_1_1 = True
                                    l_1264_guarded_1_1 = T(l_1264_guarded_1_1_0, l_1264_guarded_1_1_1)
                                    l_1264_guarded_1 = T(l_1264_guarded_1_0, l_1264_guarded_1_1)
                                    l_1264_guarded = T(l_1264_guarded_0, l_1264_guarded_1)
                                if l_165_impA:
                                    _t6 = l_162_pB
                                elif l_166_impB:
                                    _t6 = l_161_pA
                                else:
                                    _t6 = (l_161_pA + l_162_pB)
                                _e5 = T((((l_321_guarded[0] * l_1264_guarded[0]) if cse_5 else 0.0) * _t6), T(0, T(0.0, ((l_321_guarded[1][1][1] or l_1264_guarded[1][1][1]) if cse_5 else True))))[0]
                                _s4.append(_e5)
                            l_1266_enum_mass = sum(_s4)
                            l_1267_any_shared_0 = l_1266_enum_mass
                            l_1267_any_shared_1 = (l_1266_enum_mass == 0.0)
                            l_1267_any_shared = T(l_1267_any_shared_0, l_1267_any_shared_1)
                        l_1268_guarded_0 = l_1267_any_shared[0]
                        l_1268_guarded_1_0 = 0
                        l_1268_guarded_1_1_0 = 0.0
                        l_1268_guarded_1_1_1 = l_1267_any_shared[1]
                        l_1268_guarded_1_1 = T(l_1268_guarded_1_1_0, l_1268_guarded_1_1_1)
                        l_1268_guarded_1 = T(l_1268_guarded_1_0, l_1268_guarded_1_1)
                        l_1268_guarded = T(l_1268_guarded_0, l_1268_guarded_1)
                    else:
                        l_1268_guarded_0 = 0.0
                        l_1268_guarded_1_0 = 0
                        l_1268_guarded_1_1_0 = 0.0
                        l_1268_guarded_1_1_1 = True
                        l_1268_guarded_1_1 = T(l_1268_guarded_1_1_0, l_1268_guarded_1_1_1)
                        l_1268_guarded_1 = T(l_1268_guarded_1_0, l_1268_guarded_1_1)
                        l_1268_guarded = T(l_1268_guarded_0, l_1268_guarded_1)
                    if isAny(sample[0]):
                        _t7 = 1.0
                    elif sample[0]:
                        _t7 = 1.0
                    elif (True if isAny(_v2) else (False == _v2)):
                        _t7 = 1.0
                    else:
                        _t7 = 0.0
                    _e2 = T(((_t7 * l_1268_guarded[0]) * 0.5), T(0, T((0.0 if isAny(sample[0]) else 1.0), (cse_0 or l_1268_guarded[1][1][1]))))[0]
                    _s1.append(_e2)
                l_1270_enum_mass = sum(_s1)
                l_1271_any_shared_0 = l_1270_enum_mass
                l_1271_any_shared_1 = (l_1270_enum_mass == 0.0)
                l_1271_any_shared = T(l_1271_any_shared_0, l_1271_any_shared_1)
            l_r_0 = l_1271_any_shared[0]
            l_r_1_0 = 0
            l_r_1_1_0 = 0.0
            l_r_1_1_1 = l_1271_any_shared[1]
            l_r_1_1 = T(l_r_1_1_0, l_r_1_1_1)
            l_r_1 = T(l_r_1_0, l_r_1_1)
            l_r = T(l_r_0, l_r_1)
            _r0 = l_r[0]
            _r1_0 = l_r[1][0]
            _r1_1 = l_r[1][1][1]
            _r1 = T(_r1_0, _r1_1)
            return T(_r0, _r1)
        else:
            return throw("cdf(main): query value does not conform to return type Tuple TBool (ListOf TBool)")
    
    # Calculates the probability of the sample parameter being returned from the mainfunction
    # Query-type guard active: rejects a query value not matching return type Tuple TBool (ListOf TBool) (disable with --noTypeCheck).
    def forward(self, sample):
        if (isAny(sample) or (isinstance(sample, T) and (isAny(sample.t1) or isinstance(sample.t1, bool)) and (isAny(sample.t2) or (isinstance(sample.t2, InferenceList) and all((isAny(_ce0) or isinstance(_ce0, bool)) for _ce0 in sample.t2))))):
            if isAny(sample):
                l_1271_any_shared_0 = 1.0
                l_1271_any_shared_1 = False
                l_1271_any_shared = T(l_1271_any_shared_0, l_1271_any_shared_1)
            else:
                _s8 = [True, False]
                _s9 = []
                for _v10 in _s8:
                    if isAny(sample[0]):
                        cse_0 = False
                    else:
                        if isAny(_v10):
                            _t11 = True
                        elif isAny(sample[0]):
                            _t11 = True
                        else:
                            _t11 = (sample[0] == _v10)
                        cse_0 = (not(_t11))
                    if (not(cse_0)):
                        if isAny(sample[1]):
                            l_1267_any_shared_0 = 1.0
                            l_1267_any_shared_1 = False
                            l_1267_any_shared = T(l_1267_any_shared_0, l_1267_any_shared_1)
                        else:
                            if isAny(_v10):
                                cse_2 = True
                            else:
                                cse_2 = (True == _v10)
                            if cse_2:
                                cse_1 = 1.0
                            else:
                                cse_1 = 0.0
                            if (not(cse_2)):
                                cse_4 = 1.0
                            else:
                                cse_4 = (1.0 - cse_1)
                            cse_3 = isclose(cse_4, 0.0)
                            if (not(isclose(cse_1, 0.0))):
                                l_165_impA = (not(cse_2))
                            else:
                                l_165_impA = True
                            if (not(cse_3)):
                                l_166_impB = (cse_4 == 0.0)
                            else:
                                l_166_impB = True
                            _s12 = [True, False]
                            _s13 = []
                            for _v14 in _s12:
                                cse_6 = (sample[1] == EmptyInferenceList())
                                cse_5 = ((not(cse_6)) and (not(cse_6)))
                                if (not(isclose(cse_1, 0.0))):
                                    l_161_pA = (cse_1 * (9.999999999999998e-2 if (not(_v14)) else 0.9))
                                else:
                                    l_161_pA = 0.0
                                if (not(cse_3)):
                                    l_162_pB = (cse_4 * (0.8 if (not(_v14)) else 0.2))
                                else:
                                    l_162_pB = 0.0
                                if (not(cse_6)):
                                    if isAny(sample[1][0]):
                                        l_320_any_shared_0 = 1.0
                                        l_320_any_shared_1 = False
                                        l_320_any_shared = T(l_320_any_shared_0, l_320_any_shared_1)
                                    else:
                                        if (not(cse_2)):
                                            cse_8 = 1.0
                                        else:
                                            cse_8 = (1.0 - cse_1)
                                        cse_7 = isclose(cse_8, 0.0)
                                        if (not(isclose(cse_1, 0.0))):
                                            l_317_impA = (not(cse_2))
                                        else:
                                            l_317_impA = True
                                        if (not(cse_7)):
                                            l_318_impB = (cse_8 == 0.0)
                                        else:
                                            l_318_impB = True
                                        l_319_enum_mass = sum([((l_313_pA:=((cse_1 * (9.999999999999998e-2 if (not(h0)) else 0.9)) if (not(isclose(cse_1, 0.0))) else 0.0)), ((l_314_pB:=((cse_8 * (0.8 if (not(h0)) else 0.2)) if (not(cse_7)) else 0.0)), T(((((1.0 if (sample[1][0] == True) else 0.0) if h0 else 0.0) + ((1.0 if (sample[1][0] == _v14) else 0.0) if (not(h0)) else 0.0)) * (l_314_pB if l_317_impA else (l_313_pA if l_318_impB else (l_313_pA + l_314_pB)))), T(0, T(1.0, False))))[1])[1][0] for h0 in [True, False]])
                                        l_320_any_shared_0 = l_319_enum_mass
                                        l_320_any_shared_1 = (l_319_enum_mass == 0.0)
                                        l_320_any_shared = T(l_320_any_shared_0, l_320_any_shared_1)
                                    l_321_guarded_0 = l_320_any_shared[0]
                                    l_321_guarded_1_0 = 0
                                    l_321_guarded_1_1_0 = 0.0
                                    l_321_guarded_1_1_1 = l_320_any_shared[1]
                                    l_321_guarded_1_1 = T(l_321_guarded_1_1_0, l_321_guarded_1_1_1)
                                    l_321_guarded_1 = T(l_321_guarded_1_0, l_321_guarded_1_1)
                                    l_321_guarded = T(l_321_guarded_0, l_321_guarded_1)
                                else:
                                    l_321_guarded_0 = 0.0
                                    l_321_guarded_1_0 = 0
                                    l_321_guarded_1_1_0 = 0.0
                                    l_321_guarded_1_1_1 = True
                                    l_321_guarded_1_1 = T(l_321_guarded_1_1_0, l_321_guarded_1_1_1)
                                    l_321_guarded_1 = T(l_321_guarded_1_0, l_321_guarded_1_1)
                                    l_321_guarded = T(l_321_guarded_0, l_321_guarded_1)
                                if (not(cse_6)):
                                    if (not(l_321_guarded[1][1][1])):
                                        if isAny(sample[1][1:]):
                                            l_1263_any_shared_0 = 1.0
                                            l_1263_any_shared_1 = False
                                            l_1263_any_shared = T(l_1263_any_shared_0, l_1263_any_shared_1)
                                        else:
                                            if (not(cse_2)):
                                                cse_10 = 1.0
                                            else:
                                                cse_10 = (1.0 - cse_1)
                                            cse_9 = isclose(cse_10, 0.0)
                                            if (not(isclose(cse_1, 0.0))):
                                                l_338_impA = (not(cse_2))
                                            else:
                                                l_338_impA = True
                                            if (not(cse_9)):
                                                l_339_impB = (cse_10 == 0.0)
                                            else:
                                                l_339_impB = True
                                            l_1262_enum_mass = sum([((cse_12:=(sample[1][1:] == EmptyInferenceList())), ((cse_11:=((not(cse_12)) and (not(cse_12)))), ((l_334_pA:=((cse_1 * (9.999999999999998e-2 if (not(h2)) else 0.9)) if (not(isclose(cse_1, 0.0))) else 0.0)), ((l_335_pB:=((cse_10 * (0.8 if (not(h2)) else 0.2)) if (not(cse_9)) else 0.0)), ((l_1260_guarded:=((((l_1259_any_shared:=(T(1.0, False) if isAny(sample[1][1:][1:]) else ((cse_16:=(1.0 if (not(cse_2)) else (1.0 - cse_1))), ((cse_15:=isclose(cse_16, 0.0)), ((l_484_impA:=((not(cse_2)) if (not(isclose(cse_1, 0.0))) else True)), ((l_485_impB:=((cse_16 == 0.0) if (not(cse_15)) else True)), ((l_1258_enum_mass:=sum([((cse_18:=(sample[1][1:][1:] == EmptyInferenceList())), ((cse_17:=((not(cse_18)) and (not(cse_18)))), ((l_480_pA:=((cse_1 * (9.999999999999998e-2 if (not(h3)) else 0.9)) if (not(isclose(cse_1, 0.0))) else 0.0)), ((l_481_pB:=((cse_16 * (0.8 if (not(h3)) else 0.2)) if (not(cse_15)) else 0.0)), ((l_1256_guarded:=((((l_1255_any_shared:=(T(1.0, False) if isAny(sample[1][1:][1:][1:]) else ((cse_22:=(1.0 if (not(cse_2)) else (1.0 - cse_1))), ((cse_21:=isclose(cse_22, 0.0)), ((l_618_impA:=((not(cse_2)) if (not(isclose(cse_1, 0.0))) else True)), ((l_619_impB:=((cse_22 == 0.0) if (not(cse_21)) else True)), ((l_1254_enum_mass:=sum([((cse_24:=(sample[1][1:][1:][1:] == EmptyInferenceList())), ((cse_23:=((not(cse_24)) and (not(cse_24)))), ((l_614_pA:=((cse_1 * (9.999999999999998e-2 if (not(h4)) else 0.9)) if (not(isclose(cse_1, 0.0))) else 0.0)), ((l_615_pB:=((cse_22 * (0.8 if (not(h4)) else 0.2)) if (not(cse_21)) else 0.0)), ((l_1252_guarded:=((((l_1251_any_shared:=(T(1.0, False) if isAny(sample[1][1:][1:][1:][1:]) else ((cse_28:=(1.0 if (not(cse_2)) else (1.0 - cse_1))), ((cse_27:=isclose(cse_28, 0.0)), ((l_740_impA:=((not(cse_2)) if (not(isclose(cse_1, 0.0))) else True)), ((l_741_impB:=((cse_28 == 0.0) if (not(cse_27)) else True)), ((l_1250_enum_mass:=sum([((cse_30:=(sample[1][1:][1:][1:][1:] == EmptyInferenceList())), ((cse_29:=((not(cse_30)) and (not(cse_30)))), ((l_736_pA:=((cse_1 * (9.999999999999998e-2 if (not(h5)) else 0.9)) if (not(isclose(cse_1, 0.0))) else 0.0)), ((l_737_pB:=((cse_28 * (0.8 if (not(h5)) else 0.2)) if (not(cse_27)) else 0.0)), ((l_1248_guarded:=((((l_1247_any_shared:=(T(1.0, False) if isAny(sample[1][1:][1:][1:][1:][1:]) else ((cse_34:=(1.0 if (not(cse_2)) else (1.0 - cse_1))), ((cse_33:=isclose(cse_34, 0.0)), ((l_850_impA:=((not(cse_2)) if (not(isclose(cse_1, 0.0))) else True)), ((l_851_impB:=((cse_34 == 0.0) if (not(cse_33)) else True)), ((l_1246_enum_mass:=sum([((cse_36:=(sample[1][1:][1:][1:][1:][1:] == EmptyInferenceList())), ((cse_35:=((not(cse_36)) and (not(cse_36)))), ((l_846_pA:=((cse_1 * (9.999999999999998e-2 if (not(h6)) else 0.9)) if (not(isclose(cse_1, 0.0))) else 0.0)), ((l_847_pB:=((cse_34 * (0.8 if (not(h6)) else 0.2)) if (not(cse_33)) else 0.0)), ((l_1244_guarded:=((((l_1243_any_shared:=(T(1.0, False) if isAny(sample[1][1:][1:][1:][1:][1:][1:]) else ((cse_40:=(1.0 if (not(cse_2)) else (1.0 - cse_1))), ((cse_39:=isclose(cse_40, 0.0)), ((l_948_impA:=((not(cse_2)) if (not(isclose(cse_1, 0.0))) else True)), ((l_949_impB:=((cse_40 == 0.0) if (not(cse_39)) else True)), ((l_1242_enum_mass:=sum([((cse_42:=(sample[1][1:][1:][1:][1:][1:][1:] == EmptyInferenceList())), ((cse_41:=((not(cse_42)) and (not(cse_42)))), ((l_944_pA:=((cse_1 * (9.999999999999998e-2 if (not(h7)) else 0.9)) if (not(isclose(cse_1, 0.0))) else 0.0)), ((l_945_pB:=((cse_40 * (0.8 if (not(h7)) else 0.2)) if (not(cse_39)) else 0.0)), ((l_1240_guarded:=((((l_1239_any_shared:=(T(1.0, False) if isAny(sample[1][1:][1:][1:][1:][1:][1:][1:]) else ((cse_46:=(1.0 if (not(cse_2)) else (1.0 - cse_1))), ((cse_45:=isclose(cse_46, 0.0)), ((l_1034_impA:=((not(cse_2)) if (not(isclose(cse_1, 0.0))) else True)), ((l_1035_impB:=((cse_46 == 0.0) if (not(cse_45)) else True)), ((l_1238_enum_mass:=sum([((cse_48:=(sample[1][1:][1:][1:][1:][1:][1:][1:] == EmptyInferenceList())), ((cse_47:=((not(cse_48)) and (not(cse_48)))), ((l_1030_pA:=((cse_1 * (9.999999999999998e-2 if (not(h8)) else 0.9)) if (not(isclose(cse_1, 0.0))) else 0.0)), ((l_1031_pB:=((cse_46 * (0.8 if (not(h8)) else 0.2)) if (not(cse_45)) else 0.0)), ((l_1236_guarded:=((((l_1235_any_shared:=(T(1.0, False) if isAny(sample[1][1:][1:][1:][1:][1:][1:][1:][1:]) else ((cse_52:=(1.0 if (not(cse_2)) else (1.0 - cse_1))), ((cse_51:=isclose(cse_52, 0.0)), ((l_1108_impA:=((not(cse_2)) if (not(isclose(cse_1, 0.0))) else True)), ((l_1109_impB:=((cse_52 == 0.0) if (not(cse_51)) else True)), ((l_1234_enum_mass:=sum([((cse_54:=(sample[1][1:][1:][1:][1:][1:][1:][1:][1:] == EmptyInferenceList())), ((cse_53:=((not(cse_54)) and (not(cse_54)))), ((l_1104_pA:=((cse_1 * (9.999999999999998e-2 if (not(h9)) else 0.9)) if (not(isclose(cse_1, 0.0))) else 0.0)), ((l_1105_pB:=((cse_52 * (0.8 if (not(h9)) else 0.2)) if (not(cse_51)) else 0.0)), ((l_1232_guarded:=((((l_1231_any_shared:=(T(1.0, False) if isAny(sample[1][1:][1:][1:][1:][1:][1:][1:][1:][1:]) else ((cse_58:=(1.0 if (not(cse_2)) else (1.0 - cse_1))), ((cse_57:=isclose(cse_58, 0.0)), ((l_1170_impA:=((not(cse_2)) if (not(isclose(cse_1, 0.0))) else True)), ((l_1171_impB:=((cse_58 == 0.0) if (not(cse_57)) else True)), ((l_1230_enum_mass:=sum([((cse_60:=(sample[1][1:][1:][1:][1:][1:][1:][1:][1:][1:] == EmptyInferenceList())), ((cse_59:=((not(cse_60)) and (not(cse_60)))), ((l_1166_pA:=((cse_1 * (9.999999999999998e-2 if (not(h10)) else 0.9)) if (not(isclose(cse_1, 0.0))) else 0.0)), ((l_1167_pB:=((cse_58 * (0.8 if (not(h10)) else 0.2)) if (not(cse_57)) else 0.0)), ((l_1228_guarded:=((((l_1227_any_shared:=(T(1.0, False) if isAny(sample[1][1:][1:][1:][1:][1:][1:][1:][1:][1:][1:]) else ((cse_64:=(1.0 if (not(cse_2)) else (1.0 - cse_1))), ((cse_63:=isclose(cse_64, 0.0)), ((l_1220_impA:=((not(cse_2)) if (not(isclose(cse_1, 0.0))) else True)), ((l_1221_impB:=((cse_64 == 0.0) if (not(cse_63)) else True)), ((l_1226_enum_mass:=sum([((cse_65:=(sample[1][1:][1:][1:][1:][1:][1:][1:][1:][1:][1:] == ConsInferenceList((True if h10 else h11), EmptyInferenceList()))), ((l_1216_pA:=((cse_1 * (9.999999999999998e-2 if (not(h11)) else 0.9)) if (not(isclose(cse_1, 0.0))) else 0.0)), ((l_1217_pB:=((cse_64 * (0.8 if (not(h11)) else 0.2)) if (not(cse_63)) else 0.0)), T(((l_1217_pB if l_1220_impA else (l_1216_pA if l_1221_impB else (l_1216_pA + l_1217_pB))) if cse_65 else 0.0), T(0, T(1.0, (not(cse_65))))))[1])[1][0])[1] for h11 in [True, False]])), T(l_1226_enum_mass, (l_1226_enum_mass == 0.0)))[1])[1])[1])[1])[1])), T(l_1227_any_shared[0], T(0, T(0.0, l_1227_any_shared[1]))))[1] if (not((False if isAny(sample[1][1:][1:][1:][1:][1:][1:][1:][1:][1:][0]) else ((cse_62:=(True if isAny(h9) else (True == h9))), ((cse_61:=(1.0 if cse_62 else 0.0)), ((l_1197_impB:=(not(cse_62))), ((((not(cse_62)) or (not((True if isAny(h10) else (True if isAny(sample[1][1:][1:][1:][1:][1:][1:][1:][1:][1:][0]) else (sample[1][1:][1:][1:][1:][1:][1:][1:][1:][1:][0] == h10)))))) if (not(isclose(cse_61, 0.0))) else True) and ((((1.0 if l_1197_impB else (1.0 - cse_61)) == 0.0) or (not((True if isAny(sample[1][1:][1:][1:][1:][1:][1:][1:][1:][1:][0]) else (sample[1][1:][1:][1:][1:][1:][1:][1:][1:][1:][0] == False))))) if (not(isclose((1.0 if l_1197_impB else (1.0 - cse_61)), 0.0))) else True)))[1])[1])[1]))) else T(0.0, T(0, T(0.0, True)))) if (not(cse_60)) else T(0.0, T(0, T(0.0, True))))), T((((((1.0 if isAny(sample[1][1:][1:][1:][1:][1:][1:][1:][1:][1:][0]) else ((cse_68:=(True if isAny(h9) else (True == h9))), ((cse_67:=(1.0 if cse_68 else 0.0)), ((cse_66:=isclose(cse_67, 0.0)), ((l_1197_impB:=(not(cse_68))), ((cse_69:=isclose((1.0 if l_1197_impB else (1.0 - cse_67)), 0.0)), ((l_1198_pA:=((cse_67 if (True if isAny(h10) else (True if isAny(sample[1][1:][1:][1:][1:][1:][1:][1:][1:][1:][0]) else (sample[1][1:][1:][1:][1:][1:][1:][1:][1:][1:][0] == h10))) else 0.0) if (not(cse_66)) else 0.0)), ((l_1199_pB:=(((1.0 if l_1197_impB else (1.0 - cse_67)) if (True if isAny(sample[1][1:][1:][1:][1:][1:][1:][1:][1:][1:][0]) else (sample[1][1:][1:][1:][1:][1:][1:][1:][1:][1:][0] == False)) else 0.0) if (not(cse_69)) else 0.0)), (l_1199_pB if (((not(cse_68)) or (not((True if isAny(h10) else (True if isAny(sample[1][1:][1:][1:][1:][1:][1:][1:][1:][1:][0]) else (sample[1][1:][1:][1:][1:][1:][1:][1:][1:][1:][0] == h10)))))) if (not(cse_66)) else True) else (l_1198_pA if ((((1.0 if l_1197_impB else (1.0 - cse_67)) == 0.0) or (not((True if isAny(sample[1][1:][1:][1:][1:][1:][1:][1:][1:][1:][0]) else (sample[1][1:][1:][1:][1:][1:][1:][1:][1:][1:][0] == False))))) if (not(cse_69)) else True) else (l_1198_pA + l_1199_pB))))[1])[1])[1])[1])[1])[1])[1]) if (not(cse_60)) else 0.0) * l_1228_guarded[0]) if cse_59 else 0.0) * (l_1167_pB if l_1170_impA else (l_1166_pA if l_1171_impB else (l_1166_pA + l_1167_pB)))), (T(0, T((0.0 if isAny(sample[1][1:][1:][1:][1:][1:][1:][1:][1:][1:][0]) else ((cse_73:=(True if isAny(h9) else (True == h9))), ((cse_72:=(1.0 if cse_73 else 0.0)), ((0.0 if isclose(cse_72, 0.0) else 1.0) + (0.0 if isclose((1.0 if (not(cse_73)) else (1.0 - cse_72)), 0.0) else 1.0)))[1])[1]), (((False if isAny(sample[1][1:][1:][1:][1:][1:][1:][1:][1:][1:][0]) else ((cse_75:=(True if isAny(h9) else (True == h9))), ((cse_74:=(1.0 if cse_75 else 0.0)), ((l_1197_impB:=(not(cse_75))), ((((not(cse_75)) or (not((True if isAny(h10) else (True if isAny(sample[1][1:][1:][1:][1:][1:][1:][1:][1:][1:][0]) else (sample[1][1:][1:][1:][1:][1:][1:][1:][1:][1:][0] == h10)))))) if (not(isclose(cse_74, 0.0))) else True) and ((((1.0 if l_1197_impB else (1.0 - cse_74)) == 0.0) or (not((True if isAny(sample[1][1:][1:][1:][1:][1:][1:][1:][1:][1:][0]) else (sample[1][1:][1:][1:][1:][1:][1:][1:][1:][1:][0] == False))))) if (not(isclose((1.0 if l_1197_impB else (1.0 - cse_74)), 0.0))) else True)))[1])[1])[1]) if (not(cse_60)) else True) or l_1228_guarded[1][1][1]))) if cse_59 else T(0, T(0.0, True)))))[1])[1])[1][0])[1])[1] for h10 in [True, False]])), T(l_1230_enum_mass, (l_1230_enum_mass == 0.0)))[1])[1])[1])[1])[1])), T(l_1231_any_shared[0], T(0, T(0.0, l_1231_any_shared[1]))))[1] if (not((False if isAny(sample[1][1:][1:][1:][1:][1:][1:][1:][1:][0]) else ((cse_56:=(True if isAny(h8) else (True == h8))), ((cse_55:=(1.0 if cse_56 else 0.0)), ((l_1147_impB:=(not(cse_56))), ((((not(cse_56)) or (not((True if isAny(sample[1][1:][1:][1:][1:][1:][1:][1:][1:][0]) else (sample[1][1:][1:][1:][1:][1:][1:][1:][1:][0] == True))))) if (not(isclose(cse_55, 0.0))) else True) and ((((1.0 if l_1147_impB else (1.0 - cse_55)) == 0.0) or (not((True if isAny(h9) else (True if isAny(sample[1][1:][1:][1:][1:][1:][1:][1:][1:][0]) else (sample[1][1:][1:][1:][1:][1:][1:][1:][1:][0] == h9)))))) if (not(isclose((1.0 if l_1147_impB else (1.0 - cse_55)), 0.0))) else True)))[1])[1])[1]))) else T(0.0, T(0, T(0.0, True)))) if (not(cse_54)) else T(0.0, T(0, T(0.0, True))))), T((((((1.0 if isAny(sample[1][1:][1:][1:][1:][1:][1:][1:][1:][0]) else ((cse_78:=(True if isAny(h8) else (True == h8))), ((cse_77:=(1.0 if cse_78 else 0.0)), ((cse_76:=isclose(cse_77, 0.0)), ((l_1147_impB:=(not(cse_78))), ((cse_79:=isclose((1.0 if l_1147_impB else (1.0 - cse_77)), 0.0)), ((l_1148_pA:=((cse_77 if (True if isAny(sample[1][1:][1:][1:][1:][1:][1:][1:][1:][0]) else (sample[1][1:][1:][1:][1:][1:][1:][1:][1:][0] == True)) else 0.0) if (not(cse_76)) else 0.0)), ((l_1149_pB:=(((1.0 if l_1147_impB else (1.0 - cse_77)) if (True if isAny(h9) else (True if isAny(sample[1][1:][1:][1:][1:][1:][1:][1:][1:][0]) else (sample[1][1:][1:][1:][1:][1:][1:][1:][1:][0] == h9))) else 0.0) if (not(cse_79)) else 0.0)), (l_1149_pB if (((not(cse_78)) or (not((True if isAny(sample[1][1:][1:][1:][1:][1:][1:][1:][1:][0]) else (sample[1][1:][1:][1:][1:][1:][1:][1:][1:][0] == True))))) if (not(cse_76)) else True) else (l_1148_pA if ((((1.0 if l_1147_impB else (1.0 - cse_77)) == 0.0) or (not((True if isAny(h9) else (True if isAny(sample[1][1:][1:][1:][1:][1:][1:][1:][1:][0]) else (sample[1][1:][1:][1:][1:][1:][1:][1:][1:][0] == h9)))))) if (not(cse_79)) else True) else (l_1148_pA + l_1149_pB))))[1])[1])[1])[1])[1])[1])[1]) if (not(cse_54)) else 0.0) * l_1232_guarded[0]) if cse_53 else 0.0) * (l_1105_pB if l_1108_impA else (l_1104_pA if l_1109_impB else (l_1104_pA + l_1105_pB)))), (T(0, T((0.0 if isAny(sample[1][1:][1:][1:][1:][1:][1:][1:][1:][0]) else ((cse_83:=(True if isAny(h8) else (True == h8))), ((cse_82:=(1.0 if cse_83 else 0.0)), ((0.0 if isclose(cse_82, 0.0) else 1.0) + (0.0 if isclose((1.0 if (not(cse_83)) else (1.0 - cse_82)), 0.0) else 1.0)))[1])[1]), (((False if isAny(sample[1][1:][1:][1:][1:][1:][1:][1:][1:][0]) else ((cse_85:=(True if isAny(h8) else (True == h8))), ((cse_84:=(1.0 if cse_85 else 0.0)), ((l_1147_impB:=(not(cse_85))), ((((not(cse_85)) or (not((True if isAny(sample[1][1:][1:][1:][1:][1:][1:][1:][1:][0]) else (sample[1][1:][1:][1:][1:][1:][1:][1:][1:][0] == True))))) if (not(isclose(cse_84, 0.0))) else True) and ((((1.0 if l_1147_impB else (1.0 - cse_84)) == 0.0) or (not((True if isAny(h9) else (True if isAny(sample[1][1:][1:][1:][1:][1:][1:][1:][1:][0]) else (sample[1][1:][1:][1:][1:][1:][1:][1:][1:][0] == h9)))))) if (not(isclose((1.0 if l_1147_impB else (1.0 - cse_84)), 0.0))) else True)))[1])[1])[1]) if (not(cse_54)) else True) or l_1232_guarded[1][1][1]))) if cse_53 else T(0, T(0.0, True)))))[1])[1])[1][0])[1])[1] for h9 in [True, False]])), T(l_1234_enum_mass, (l_1234_enum_mass == 0.0)))[1])[1])[1])[1])[1])), T(l_1235_any_shared[0], T(0, T(0.0, l_1235_any_shared[1]))))[1] if (not((False if isAny(sample[1][1:][1:][1:][1:][1:][1:][1:][0]) else ((cse_50:=(True if isAny(h7) else (True == h7))), ((cse_49:=(1.0 if cse_50 else 0.0)), ((l_1085_impB:=(not(cse_50))), ((((not(cse_50)) or (not((True if isAny(h8) else (True if isAny(sample[1][1:][1:][1:][1:][1:][1:][1:][0]) else (sample[1][1:][1:][1:][1:][1:][1:][1:][0] == h8)))))) if (not(isclose(cse_49, 0.0))) else True) and ((((1.0 if l_1085_impB else (1.0 - cse_49)) == 0.0) or (not((True if isAny(sample[1][1:][1:][1:][1:][1:][1:][1:][0]) else (sample[1][1:][1:][1:][1:][1:][1:][1:][0] == False))))) if (not(isclose((1.0 if l_1085_impB else (1.0 - cse_49)), 0.0))) else True)))[1])[1])[1]))) else T(0.0, T(0, T(0.0, True)))) if (not(cse_48)) else T(0.0, T(0, T(0.0, True))))), T((((((1.0 if isAny(sample[1][1:][1:][1:][1:][1:][1:][1:][0]) else ((cse_88:=(True if isAny(h7) else (True == h7))), ((cse_87:=(1.0 if cse_88 else 0.0)), ((cse_86:=isclose(cse_87, 0.0)), ((l_1085_impB:=(not(cse_88))), ((cse_89:=isclose((1.0 if l_1085_impB else (1.0 - cse_87)), 0.0)), ((l_1086_pA:=((cse_87 if (True if isAny(h8) else (True if isAny(sample[1][1:][1:][1:][1:][1:][1:][1:][0]) else (sample[1][1:][1:][1:][1:][1:][1:][1:][0] == h8))) else 0.0) if (not(cse_86)) else 0.0)), ((l_1087_pB:=(((1.0 if l_1085_impB else (1.0 - cse_87)) if (True if isAny(sample[1][1:][1:][1:][1:][1:][1:][1:][0]) else (sample[1][1:][1:][1:][1:][1:][1:][1:][0] == False)) else 0.0) if (not(cse_89)) else 0.0)), (l_1087_pB if (((not(cse_88)) or (not((True if isAny(h8) else (True if isAny(sample[1][1:][1:][1:][1:][1:][1:][1:][0]) else (sample[1][1:][1:][1:][1:][1:][1:][1:][0] == h8)))))) if (not(cse_86)) else True) else (l_1086_pA if ((((1.0 if l_1085_impB else (1.0 - cse_87)) == 0.0) or (not((True if isAny(sample[1][1:][1:][1:][1:][1:][1:][1:][0]) else (sample[1][1:][1:][1:][1:][1:][1:][1:][0] == False))))) if (not(cse_89)) else True) else (l_1086_pA + l_1087_pB))))[1])[1])[1])[1])[1])[1])[1]) if (not(cse_48)) else 0.0) * l_1236_guarded[0]) if cse_47 else 0.0) * (l_1031_pB if l_1034_impA else (l_1030_pA if l_1035_impB else (l_1030_pA + l_1031_pB)))), (T(0, T((0.0 if isAny(sample[1][1:][1:][1:][1:][1:][1:][1:][0]) else ((cse_93:=(True if isAny(h7) else (True == h7))), ((cse_92:=(1.0 if cse_93 else 0.0)), ((0.0 if isclose(cse_92, 0.0) else 1.0) + (0.0 if isclose((1.0 if (not(cse_93)) else (1.0 - cse_92)), 0.0) else 1.0)))[1])[1]), (((False if isAny(sample[1][1:][1:][1:][1:][1:][1:][1:][0]) else ((cse_95:=(True if isAny(h7) else (True == h7))), ((cse_94:=(1.0 if cse_95 else 0.0)), ((l_1085_impB:=(not(cse_95))), ((((not(cse_95)) or (not((True if isAny(h8) else (True if isAny(sample[1][1:][1:][1:][1:][1:][1:][1:][0]) else (sample[1][1:][1:][1:][1:][1:][1:][1:][0] == h8)))))) if (not(isclose(cse_94, 0.0))) else True) and ((((1.0 if l_1085_impB else (1.0 - cse_94)) == 0.0) or (not((True if isAny(sample[1][1:][1:][1:][1:][1:][1:][1:][0]) else (sample[1][1:][1:][1:][1:][1:][1:][1:][0] == False))))) if (not(isclose((1.0 if l_1085_impB else (1.0 - cse_94)), 0.0))) else True)))[1])[1])[1]) if (not(cse_48)) else True) or l_1236_guarded[1][1][1]))) if cse_47 else T(0, T(0.0, True)))))[1])[1])[1][0])[1])[1] for h8 in [True, False]])), T(l_1238_enum_mass, (l_1238_enum_mass == 0.0)))[1])[1])[1])[1])[1])), T(l_1239_any_shared[0], T(0, T(0.0, l_1239_any_shared[1]))))[1] if (not((False if isAny(sample[1][1:][1:][1:][1:][1:][1:][0]) else ((cse_44:=(True if isAny(h6) else (True == h6))), ((cse_43:=(1.0 if cse_44 else 0.0)), ((l_1011_impB:=(not(cse_44))), ((((not(cse_44)) or (not((True if isAny(sample[1][1:][1:][1:][1:][1:][1:][0]) else (sample[1][1:][1:][1:][1:][1:][1:][0] == True))))) if (not(isclose(cse_43, 0.0))) else True) and ((((1.0 if l_1011_impB else (1.0 - cse_43)) == 0.0) or (not((True if isAny(h7) else (True if isAny(sample[1][1:][1:][1:][1:][1:][1:][0]) else (sample[1][1:][1:][1:][1:][1:][1:][0] == h7)))))) if (not(isclose((1.0 if l_1011_impB else (1.0 - cse_43)), 0.0))) else True)))[1])[1])[1]))) else T(0.0, T(0, T(0.0, True)))) if (not(cse_42)) else T(0.0, T(0, T(0.0, True))))), T((((((1.0 if isAny(sample[1][1:][1:][1:][1:][1:][1:][0]) else ((cse_98:=(True if isAny(h6) else (True == h6))), ((cse_97:=(1.0 if cse_98 else 0.0)), ((cse_96:=isclose(cse_97, 0.0)), ((l_1011_impB:=(not(cse_98))), ((cse_99:=isclose((1.0 if l_1011_impB else (1.0 - cse_97)), 0.0)), ((l_1012_pA:=((cse_97 if (True if isAny(sample[1][1:][1:][1:][1:][1:][1:][0]) else (sample[1][1:][1:][1:][1:][1:][1:][0] == True)) else 0.0) if (not(cse_96)) else 0.0)), ((l_1013_pB:=(((1.0 if l_1011_impB else (1.0 - cse_97)) if (True if isAny(h7) else (True if isAny(sample[1][1:][1:][1:][1:][1:][1:][0]) else (sample[1][1:][1:][1:][1:][1:][1:][0] == h7))) else 0.0) if (not(cse_99)) else 0.0)), (l_1013_pB if (((not(cse_98)) or (not((True if isAny(sample[1][1:][1:][1:][1:][1:][1:][0]) else (sample[1][1:][1:][1:][1:][1:][1:][0] == True))))) if (not(cse_96)) else True) else (l_1012_pA if ((((1.0 if l_1011_impB else (1.0 - cse_97)) == 0.0) or (not((True if isAny(h7) else (True if isAny(sample[1][1:][1:][1:][1:][1:][1:][0]) else (sample[1][1:][1:][1:][1:][1:][1:][0] == h7)))))) if (not(cse_99)) else True) else (l_1012_pA + l_1013_pB))))[1])[1])[1])[1])[1])[1])[1]) if (not(cse_42)) else 0.0) * l_1240_guarded[0]) if cse_41 else 0.0) * (l_945_pB if l_948_impA else (l_944_pA if l_949_impB else (l_944_pA + l_945_pB)))), (T(0, T((0.0 if isAny(sample[1][1:][1:][1:][1:][1:][1:][0]) else ((cse_103:=(True if isAny(h6) else (True == h6))), ((cse_102:=(1.0 if cse_103 else 0.0)), ((0.0 if isclose(cse_102, 0.0) else 1.0) + (0.0 if isclose((1.0 if (not(cse_103)) else (1.0 - cse_102)), 0.0) else 1.0)))[1])[1]), (((False if isAny(sample[1][1:][1:][1:][1:][1:][1:][0]) else ((cse_105:=(True if isAny(h6) else (True == h6))), ((cse_104:=(1.0 if cse_105 else 0.0)), ((l_1011_impB:=(not(cse_105))), ((((not(cse_105)) or (not((True if isAny(sample[1][1:][1:][1:][1:][1:][1:][0]) else (sample[1][1:][1:][1:][1:][1:][1:][0] == True))))) if (not(isclose(cse_104, 0.0))) else True) and ((((1.0 if l_1011_impB else (1.0 - cse_104)) == 0.0) or (not((True if isAny(h7) else (True if isAny(sample[1][1:][1:][1:][1:][1:][1:][0]) else (sample[1][1:][1:][1:][1:][1:][1:][0] == h7)))))) if (not(isclose((1.0 if l_1011_impB else (1.0 - cse_104)), 0.0))) else True)))[1])[1])[1]) if (not(cse_42)) else True) or l_1240_guarded[1][1][1]))) if cse_41 else T(0, T(0.0, True)))))[1])[1])[1][0])[1])[1] for h7 in [True, False]])), T(l_1242_enum_mass, (l_1242_enum_mass == 0.0)))[1])[1])[1])[1])[1])), T(l_1243_any_shared[0], T(0, T(0.0, l_1243_any_shared[1]))))[1] if (not((False if isAny(sample[1][1:][1:][1:][1:][1:][0]) else ((cse_38:=(True if isAny(h5) else (True == h5))), ((cse_37:=(1.0 if cse_38 else 0.0)), ((l_925_impB:=(not(cse_38))), ((((not(cse_38)) or (not((True if isAny(h6) else (True if isAny(sample[1][1:][1:][1:][1:][1:][0]) else (sample[1][1:][1:][1:][1:][1:][0] == h6)))))) if (not(isclose(cse_37, 0.0))) else True) and ((((1.0 if l_925_impB else (1.0 - cse_37)) == 0.0) or (not((True if isAny(sample[1][1:][1:][1:][1:][1:][0]) else (sample[1][1:][1:][1:][1:][1:][0] == False))))) if (not(isclose((1.0 if l_925_impB else (1.0 - cse_37)), 0.0))) else True)))[1])[1])[1]))) else T(0.0, T(0, T(0.0, True)))) if (not(cse_36)) else T(0.0, T(0, T(0.0, True))))), T((((((1.0 if isAny(sample[1][1:][1:][1:][1:][1:][0]) else ((cse_108:=(True if isAny(h5) else (True == h5))), ((cse_107:=(1.0 if cse_108 else 0.0)), ((cse_106:=isclose(cse_107, 0.0)), ((l_925_impB:=(not(cse_108))), ((cse_109:=isclose((1.0 if l_925_impB else (1.0 - cse_107)), 0.0)), ((l_926_pA:=((cse_107 if (True if isAny(h6) else (True if isAny(sample[1][1:][1:][1:][1:][1:][0]) else (sample[1][1:][1:][1:][1:][1:][0] == h6))) else 0.0) if (not(cse_106)) else 0.0)), ((l_927_pB:=(((1.0 if l_925_impB else (1.0 - cse_107)) if (True if isAny(sample[1][1:][1:][1:][1:][1:][0]) else (sample[1][1:][1:][1:][1:][1:][0] == False)) else 0.0) if (not(cse_109)) else 0.0)), (l_927_pB if (((not(cse_108)) or (not((True if isAny(h6) else (True if isAny(sample[1][1:][1:][1:][1:][1:][0]) else (sample[1][1:][1:][1:][1:][1:][0] == h6)))))) if (not(cse_106)) else True) else (l_926_pA if ((((1.0 if l_925_impB else (1.0 - cse_107)) == 0.0) or (not((True if isAny(sample[1][1:][1:][1:][1:][1:][0]) else (sample[1][1:][1:][1:][1:][1:][0] == False))))) if (not(cse_109)) else True) else (l_926_pA + l_927_pB))))[1])[1])[1])[1])[1])[1])[1]) if (not(cse_36)) else 0.0) * l_1244_guarded[0]) if cse_35 else 0.0) * (l_847_pB if l_850_impA else (l_846_pA if l_851_impB else (l_846_pA + l_847_pB)))), (T(0, T((0.0 if isAny(sample[1][1:][1:][1:][1:][1:][0]) else ((cse_113:=(True if isAny(h5) else (True == h5))), ((cse_112:=(1.0 if cse_113 else 0.0)), ((0.0 if isclose(cse_112, 0.0) else 1.0) + (0.0 if isclose((1.0 if (not(cse_113)) else (1.0 - cse_112)), 0.0) else 1.0)))[1])[1]), (((False if isAny(sample[1][1:][1:][1:][1:][1:][0]) else ((cse_115:=(True if isAny(h5) else (True == h5))), ((cse_114:=(1.0 if cse_115 else 0.0)), ((l_925_impB:=(not(cse_115))), ((((not(cse_115)) or (not((True if isAny(h6) else (True if isAny(sample[1][1:][1:][1:][1:][1:][0]) else (sample[1][1:][1:][1:][1:][1:][0] == h6)))))) if (not(isclose(cse_114, 0.0))) else True) and ((((1.0 if l_925_impB else (1.0 - cse_114)) == 0.0) or (not((True if isAny(sample[1][1:][1:][1:][1:][1:][0]) else (sample[1][1:][1:][1:][1:][1:][0] == False))))) if (not(isclose((1.0 if l_925_impB else (1.0 - cse_114)), 0.0))) else True)))[1])[1])[1]) if (not(cse_36)) else True) or l_1244_guarded[1][1][1]))) if cse_35 else T(0, T(0.0, True)))))[1])[1])[1][0])[1])[1] for h6 in [True, False]])), T(l_1246_enum_mass, (l_1246_enum_mass == 0.0)))[1])[1])[1])[1])[1])), T(l_1247_any_shared[0], T(0, T(0.0, l_1247_any_shared[1]))))[1] if (not((False if isAny(sample[1][1:][1:][1:][1:][0]) else ((cse_32:=(True if isAny(h4) else (True == h4))), ((cse_31:=(1.0 if cse_32 else 0.0)), ((l_827_impB:=(not(cse_32))), ((((not(cse_32)) or (not((True if isAny(sample[1][1:][1:][1:][1:][0]) else (sample[1][1:][1:][1:][1:][0] == True))))) if (not(isclose(cse_31, 0.0))) else True) and ((((1.0 if l_827_impB else (1.0 - cse_31)) == 0.0) or (not((True if isAny(h5) else (True if isAny(sample[1][1:][1:][1:][1:][0]) else (sample[1][1:][1:][1:][1:][0] == h5)))))) if (not(isclose((1.0 if l_827_impB else (1.0 - cse_31)), 0.0))) else True)))[1])[1])[1]))) else T(0.0, T(0, T(0.0, True)))) if (not(cse_30)) else T(0.0, T(0, T(0.0, True))))), T((((((1.0 if isAny(sample[1][1:][1:][1:][1:][0]) else ((cse_118:=(True if isAny(h4) else (True == h4))), ((cse_117:=(1.0 if cse_118 else 0.0)), ((cse_116:=isclose(cse_117, 0.0)), ((l_827_impB:=(not(cse_118))), ((cse_119:=isclose((1.0 if l_827_impB else (1.0 - cse_117)), 0.0)), ((l_828_pA:=((cse_117 if (True if isAny(sample[1][1:][1:][1:][1:][0]) else (sample[1][1:][1:][1:][1:][0] == True)) else 0.0) if (not(cse_116)) else 0.0)), ((l_829_pB:=(((1.0 if l_827_impB else (1.0 - cse_117)) if (True if isAny(h5) else (True if isAny(sample[1][1:][1:][1:][1:][0]) else (sample[1][1:][1:][1:][1:][0] == h5))) else 0.0) if (not(cse_119)) else 0.0)), (l_829_pB if (((not(cse_118)) or (not((True if isAny(sample[1][1:][1:][1:][1:][0]) else (sample[1][1:][1:][1:][1:][0] == True))))) if (not(cse_116)) else True) else (l_828_pA if ((((1.0 if l_827_impB else (1.0 - cse_117)) == 0.0) or (not((True if isAny(h5) else (True if isAny(sample[1][1:][1:][1:][1:][0]) else (sample[1][1:][1:][1:][1:][0] == h5)))))) if (not(cse_119)) else True) else (l_828_pA + l_829_pB))))[1])[1])[1])[1])[1])[1])[1]) if (not(cse_30)) else 0.0) * l_1248_guarded[0]) if cse_29 else 0.0) * (l_737_pB if l_740_impA else (l_736_pA if l_741_impB else (l_736_pA + l_737_pB)))), (T(0, T((0.0 if isAny(sample[1][1:][1:][1:][1:][0]) else ((cse_123:=(True if isAny(h4) else (True == h4))), ((cse_122:=(1.0 if cse_123 else 0.0)), ((0.0 if isclose(cse_122, 0.0) else 1.0) + (0.0 if isclose((1.0 if (not(cse_123)) else (1.0 - cse_122)), 0.0) else 1.0)))[1])[1]), (((False if isAny(sample[1][1:][1:][1:][1:][0]) else ((cse_125:=(True if isAny(h4) else (True == h4))), ((cse_124:=(1.0 if cse_125 else 0.0)), ((l_827_impB:=(not(cse_125))), ((((not(cse_125)) or (not((True if isAny(sample[1][1:][1:][1:][1:][0]) else (sample[1][1:][1:][1:][1:][0] == True))))) if (not(isclose(cse_124, 0.0))) else True) and ((((1.0 if l_827_impB else (1.0 - cse_124)) == 0.0) or (not((True if isAny(h5) else (True if isAny(sample[1][1:][1:][1:][1:][0]) else (sample[1][1:][1:][1:][1:][0] == h5)))))) if (not(isclose((1.0 if l_827_impB else (1.0 - cse_124)), 0.0))) else True)))[1])[1])[1]) if (not(cse_30)) else True) or l_1248_guarded[1][1][1]))) if cse_29 else T(0, T(0.0, True)))))[1])[1])[1][0])[1])[1] for h5 in [True, False]])), T(l_1250_enum_mass, (l_1250_enum_mass == 0.0)))[1])[1])[1])[1])[1])), T(l_1251_any_shared[0], T(0, T(0.0, l_1251_any_shared[1]))))[1] if (not((False if isAny(sample[1][1:][1:][1:][0]) else ((cse_26:=(True if isAny(h3) else (True == h3))), ((cse_25:=(1.0 if cse_26 else 0.0)), ((l_717_impB:=(not(cse_26))), ((((not(cse_26)) or (not((True if isAny(h4) else (True if isAny(sample[1][1:][1:][1:][0]) else (sample[1][1:][1:][1:][0] == h4)))))) if (not(isclose(cse_25, 0.0))) else True) and ((((1.0 if l_717_impB else (1.0 - cse_25)) == 0.0) or (not((True if isAny(sample[1][1:][1:][1:][0]) else (sample[1][1:][1:][1:][0] == False))))) if (not(isclose((1.0 if l_717_impB else (1.0 - cse_25)), 0.0))) else True)))[1])[1])[1]))) else T(0.0, T(0, T(0.0, True)))) if (not(cse_24)) else T(0.0, T(0, T(0.0, True))))), T((((((1.0 if isAny(sample[1][1:][1:][1:][0]) else ((cse_128:=(True if isAny(h3) else (True == h3))), ((cse_127:=(1.0 if cse_128 else 0.0)), ((cse_126:=isclose(cse_127, 0.0)), ((l_717_impB:=(not(cse_128))), ((cse_129:=isclose((1.0 if l_717_impB else (1.0 - cse_127)), 0.0)), ((l_718_pA:=((cse_127 if (True if isAny(h4) else (True if isAny(sample[1][1:][1:][1:][0]) else (sample[1][1:][1:][1:][0] == h4))) else 0.0) if (not(cse_126)) else 0.0)), ((l_719_pB:=(((1.0 if l_717_impB else (1.0 - cse_127)) if (True if isAny(sample[1][1:][1:][1:][0]) else (sample[1][1:][1:][1:][0] == False)) else 0.0) if (not(cse_129)) else 0.0)), (l_719_pB if (((not(cse_128)) or (not((True if isAny(h4) else (True if isAny(sample[1][1:][1:][1:][0]) else (sample[1][1:][1:][1:][0] == h4)))))) if (not(cse_126)) else True) else (l_718_pA if ((((1.0 if l_717_impB else (1.0 - cse_127)) == 0.0) or (not((True if isAny(sample[1][1:][1:][1:][0]) else (sample[1][1:][1:][1:][0] == False))))) if (not(cse_129)) else True) else (l_718_pA + l_719_pB))))[1])[1])[1])[1])[1])[1])[1]) if (not(cse_24)) else 0.0) * l_1252_guarded[0]) if cse_23 else 0.0) * (l_615_pB if l_618_impA else (l_614_pA if l_619_impB else (l_614_pA + l_615_pB)))), (T(0, T((0.0 if isAny(sample[1][1:][1:][1:][0]) else ((cse_133:=(True if isAny(h3) else (True == h3))), ((cse_132:=(1.0 if cse_133 else 0.0)), ((0.0 if isclose(cse_132, 0.0) else 1.0) + (0.0 if isclose((1.0 if (not(cse_133)) else (1.0 - cse_132)), 0.0) else 1.0)))[1])[1]), (((False if isAny(sample[1][1:][1:][1:][0]) else ((cse_135:=(True if isAny(h3) else (True == h3))), ((cse_134:=(1.0 if cse_135 else 0.0)), ((l_717_impB:=(not(cse_135))), ((((not(cse_135)) or (not((True if isAny(h4) else (True if isAny(sample[1][1:][1:][1:][0]) else (sample[1][1:][1:][1:][0] == h4)))))) if (not(isclose(cse_134, 0.0))) else True) and ((((1.0 if l_717_impB else (1.0 - cse_134)) == 0.0) or (not((True if isAny(sample[1][1:][1:][1:][0]) else (sample[1][1:][1:][1:][0] == False))))) if (not(isclose((1.0 if l_717_impB else (1.0 - cse_134)), 0.0))) else True)))[1])[1])[1]) if (not(cse_24)) else True) or l_1252_guarded[1][1][1]))) if cse_23 else T(0, T(0.0, True)))))[1])[1])[1][0])[1])[1] for h4 in [True, False]])), T(l_1254_enum_mass, (l_1254_enum_mass == 0.0)))[1])[1])[1])[1])[1])), T(l_1255_any_shared[0], T(0, T(0.0, l_1255_any_shared[1]))))[1] if (not((False if isAny(sample[1][1:][1:][0]) else ((cse_20:=(True if isAny(h2) else (True == h2))), ((cse_19:=(1.0 if cse_20 else 0.0)), ((l_595_impB:=(not(cse_20))), ((((not(cse_20)) or (not((True if isAny(sample[1][1:][1:][0]) else (sample[1][1:][1:][0] == True))))) if (not(isclose(cse_19, 0.0))) else True) and ((((1.0 if l_595_impB else (1.0 - cse_19)) == 0.0) or (not((True if isAny(h3) else (True if isAny(sample[1][1:][1:][0]) else (sample[1][1:][1:][0] == h3)))))) if (not(isclose((1.0 if l_595_impB else (1.0 - cse_19)), 0.0))) else True)))[1])[1])[1]))) else T(0.0, T(0, T(0.0, True)))) if (not(cse_18)) else T(0.0, T(0, T(0.0, True))))), T((((((1.0 if isAny(sample[1][1:][1:][0]) else ((cse_138:=(True if isAny(h2) else (True == h2))), ((cse_137:=(1.0 if cse_138 else 0.0)), ((cse_136:=isclose(cse_137, 0.0)), ((l_595_impB:=(not(cse_138))), ((cse_139:=isclose((1.0 if l_595_impB else (1.0 - cse_137)), 0.0)), ((l_596_pA:=((cse_137 if (True if isAny(sample[1][1:][1:][0]) else (sample[1][1:][1:][0] == True)) else 0.0) if (not(cse_136)) else 0.0)), ((l_597_pB:=(((1.0 if l_595_impB else (1.0 - cse_137)) if (True if isAny(h3) else (True if isAny(sample[1][1:][1:][0]) else (sample[1][1:][1:][0] == h3))) else 0.0) if (not(cse_139)) else 0.0)), (l_597_pB if (((not(cse_138)) or (not((True if isAny(sample[1][1:][1:][0]) else (sample[1][1:][1:][0] == True))))) if (not(cse_136)) else True) else (l_596_pA if ((((1.0 if l_595_impB else (1.0 - cse_137)) == 0.0) or (not((True if isAny(h3) else (True if isAny(sample[1][1:][1:][0]) else (sample[1][1:][1:][0] == h3)))))) if (not(cse_139)) else True) else (l_596_pA + l_597_pB))))[1])[1])[1])[1])[1])[1])[1]) if (not(cse_18)) else 0.0) * l_1256_guarded[0]) if cse_17 else 0.0) * (l_481_pB if l_484_impA else (l_480_pA if l_485_impB else (l_480_pA + l_481_pB)))), (T(0, T((0.0 if isAny(sample[1][1:][1:][0]) else ((cse_143:=(True if isAny(h2) else (True == h2))), ((cse_142:=(1.0 if cse_143 else 0.0)), ((0.0 if isclose(cse_142, 0.0) else 1.0) + (0.0 if isclose((1.0 if (not(cse_143)) else (1.0 - cse_142)), 0.0) else 1.0)))[1])[1]), (((False if isAny(sample[1][1:][1:][0]) else ((cse_145:=(True if isAny(h2) else (True == h2))), ((cse_144:=(1.0 if cse_145 else 0.0)), ((l_595_impB:=(not(cse_145))), ((((not(cse_145)) or (not((True if isAny(sample[1][1:][1:][0]) else (sample[1][1:][1:][0] == True))))) if (not(isclose(cse_144, 0.0))) else True) and ((((1.0 if l_595_impB else (1.0 - cse_144)) == 0.0) or (not((True if isAny(h3) else (True if isAny(sample[1][1:][1:][0]) else (sample[1][1:][1:][0] == h3)))))) if (not(isclose((1.0 if l_595_impB else (1.0 - cse_144)), 0.0))) else True)))[1])[1])[1]) if (not(cse_18)) else True) or l_1256_guarded[1][1][1]))) if cse_17 else T(0, T(0.0, True)))))[1])[1])[1][0])[1])[1] for h3 in [True, False]])), T(l_1258_enum_mass, (l_1258_enum_mass == 0.0)))[1])[1])[1])[1])[1])), T(l_1259_any_shared[0], T(0, T(0.0, l_1259_any_shared[1]))))[1] if (not((False if isAny(sample[1][1:][0]) else ((cse_14:=(True if isAny(_v14) else (True == _v14))), ((cse_13:=(1.0 if cse_14 else 0.0)), ((l_461_impB:=(not(cse_14))), ((((not(cse_14)) or (not((True if isAny(h2) else (True if isAny(sample[1][1:][0]) else (sample[1][1:][0] == h2)))))) if (not(isclose(cse_13, 0.0))) else True) and ((((1.0 if l_461_impB else (1.0 - cse_13)) == 0.0) or (not((True if isAny(sample[1][1:][0]) else (sample[1][1:][0] == False))))) if (not(isclose((1.0 if l_461_impB else (1.0 - cse_13)), 0.0))) else True)))[1])[1])[1]))) else T(0.0, T(0, T(0.0, True)))) if (not(cse_12)) else T(0.0, T(0, T(0.0, True))))), T((((((1.0 if isAny(sample[1][1:][0]) else ((cse_148:=(True if isAny(_v14) else (True == _v14))), ((cse_147:=(1.0 if cse_148 else 0.0)), ((cse_146:=isclose(cse_147, 0.0)), ((l_461_impB:=(not(cse_148))), ((cse_149:=isclose((1.0 if l_461_impB else (1.0 - cse_147)), 0.0)), ((l_462_pA:=((cse_147 if (True if isAny(h2) else (True if isAny(sample[1][1:][0]) else (sample[1][1:][0] == h2))) else 0.0) if (not(cse_146)) else 0.0)), ((l_463_pB:=(((1.0 if l_461_impB else (1.0 - cse_147)) if (True if isAny(sample[1][1:][0]) else (sample[1][1:][0] == False)) else 0.0) if (not(cse_149)) else 0.0)), (l_463_pB if (((not(cse_148)) or (not((True if isAny(h2) else (True if isAny(sample[1][1:][0]) else (sample[1][1:][0] == h2)))))) if (not(cse_146)) else True) else (l_462_pA if ((((1.0 if l_461_impB else (1.0 - cse_147)) == 0.0) or (not((True if isAny(sample[1][1:][0]) else (sample[1][1:][0] == False))))) if (not(cse_149)) else True) else (l_462_pA + l_463_pB))))[1])[1])[1])[1])[1])[1])[1]) if (not(cse_12)) else 0.0) * l_1260_guarded[0]) if cse_11 else 0.0) * (l_335_pB if l_338_impA else (l_334_pA if l_339_impB else (l_334_pA + l_335_pB)))), (T(0, T((0.0 if isAny(sample[1][1:][0]) else ((cse_153:=(True if isAny(_v14) else (True == _v14))), ((cse_152:=(1.0 if cse_153 else 0.0)), ((0.0 if isclose(cse_152, 0.0) else 1.0) + (0.0 if isclose((1.0 if (not(cse_153)) else (1.0 - cse_152)), 0.0) else 1.0)))[1])[1]), (((False if isAny(sample[1][1:][0]) else ((cse_155:=(True if isAny(_v14) else (True == _v14))), ((cse_154:=(1.0 if cse_155 else 0.0)), ((l_461_impB:=(not(cse_155))), ((((not(cse_155)) or (not((True if isAny(h2) else (True if isAny(sample[1][1:][0]) else (sample[1][1:][0] == h2)))))) if (not(isclose(cse_154, 0.0))) else True) and ((((1.0 if l_461_impB else (1.0 - cse_154)) == 0.0) or (not((True if isAny(sample[1][1:][0]) else (sample[1][1:][0] == False))))) if (not(isclose((1.0 if l_461_impB else (1.0 - cse_154)), 0.0))) else True)))[1])[1])[1]) if (not(cse_12)) else True) or l_1260_guarded[1][1][1]))) if cse_11 else T(0, T(0.0, True)))))[1])[1])[1][0])[1])[1] for h2 in [True, False]])
                                            l_1263_any_shared_0 = l_1262_enum_mass
                                            l_1263_any_shared_1 = (l_1262_enum_mass == 0.0)
                                            l_1263_any_shared = T(l_1263_any_shared_0, l_1263_any_shared_1)
                                        l_1264_guarded_0 = l_1263_any_shared[0]
                                        l_1264_guarded_1_0 = 0
                                        l_1264_guarded_1_1_0 = 0.0
                                        l_1264_guarded_1_1_1 = l_1263_any_shared[1]
                                        l_1264_guarded_1_1 = T(l_1264_guarded_1_1_0, l_1264_guarded_1_1_1)
                                        l_1264_guarded_1 = T(l_1264_guarded_1_0, l_1264_guarded_1_1)
                                        l_1264_guarded = T(l_1264_guarded_0, l_1264_guarded_1)
                                    else:
                                        l_1264_guarded_0 = 0.0
                                        l_1264_guarded_1_0 = 0
                                        l_1264_guarded_1_1_0 = 0.0
                                        l_1264_guarded_1_1_1 = True
                                        l_1264_guarded_1_1 = T(l_1264_guarded_1_1_0, l_1264_guarded_1_1_1)
                                        l_1264_guarded_1 = T(l_1264_guarded_1_0, l_1264_guarded_1_1)
                                        l_1264_guarded = T(l_1264_guarded_0, l_1264_guarded_1)
                                else:
                                    l_1264_guarded_0 = 0.0
                                    l_1264_guarded_1_0 = 0
                                    l_1264_guarded_1_1_0 = 0.0
                                    l_1264_guarded_1_1_1 = True
                                    l_1264_guarded_1_1 = T(l_1264_guarded_1_1_0, l_1264_guarded_1_1_1)
                                    l_1264_guarded_1 = T(l_1264_guarded_1_0, l_1264_guarded_1_1)
                                    l_1264_guarded = T(l_1264_guarded_0, l_1264_guarded_1)
                                if l_165_impA:
                                    _t15 = l_162_pB
                                elif l_166_impB:
                                    _t15 = l_161_pA
                                else:
                                    _t15 = (l_161_pA + l_162_pB)
                                _e14 = T((((l_321_guarded[0] * l_1264_guarded[0]) if cse_5 else 0.0) * _t15), T(0, T(0.0, ((l_321_guarded[1][1][1] or l_1264_guarded[1][1][1]) if cse_5 else True))))[0]
                                _s13.append(_e14)
                            l_1266_enum_mass = sum(_s13)
                            l_1267_any_shared_0 = l_1266_enum_mass
                            l_1267_any_shared_1 = (l_1266_enum_mass == 0.0)
                            l_1267_any_shared = T(l_1267_any_shared_0, l_1267_any_shared_1)
                        l_1268_guarded_0 = l_1267_any_shared[0]
                        l_1268_guarded_1_0 = 0
                        l_1268_guarded_1_1_0 = 0.0
                        l_1268_guarded_1_1_1 = l_1267_any_shared[1]
                        l_1268_guarded_1_1 = T(l_1268_guarded_1_1_0, l_1268_guarded_1_1_1)
                        l_1268_guarded_1 = T(l_1268_guarded_1_0, l_1268_guarded_1_1)
                        l_1268_guarded = T(l_1268_guarded_0, l_1268_guarded_1)
                    else:
                        l_1268_guarded_0 = 0.0
                        l_1268_guarded_1_0 = 0
                        l_1268_guarded_1_1_0 = 0.0
                        l_1268_guarded_1_1_1 = True
                        l_1268_guarded_1_1 = T(l_1268_guarded_1_1_0, l_1268_guarded_1_1_1)
                        l_1268_guarded_1 = T(l_1268_guarded_1_0, l_1268_guarded_1_1)
                        l_1268_guarded = T(l_1268_guarded_0, l_1268_guarded_1)
                    if isAny(sample[0]):
                        _t16 = 1.0
                    else:
                        if isAny(_v10):
                            _t17 = True
                        elif isAny(sample[0]):
                            _t17 = True
                        else:
                            _t17 = (sample[0] == _v10)
                        if _t17:
                            _t16 = 1.0
                        else:
                            _t16 = 0.0
                    _e10 = T(((_t16 * l_1268_guarded[0]) * 0.5), T(0, T((0.0 if isAny(sample[0]) else 1.0), (cse_0 or l_1268_guarded[1][1][1]))))[0]
                    _s9.append(_e10)
                l_1270_enum_mass = sum(_s9)
                l_1271_any_shared_0 = l_1270_enum_mass
                l_1271_any_shared_1 = (l_1270_enum_mass == 0.0)
                l_1271_any_shared = T(l_1271_any_shared_0, l_1271_any_shared_1)
            l_r_0 = l_1271_any_shared[0]
            l_r_1_0 = 0
            l_r_1_1_0 = 0.0
            l_r_1_1_1 = l_1271_any_shared[1]
            l_r_1_1 = T(l_r_1_1_0, l_r_1_1_1)
            l_r_1 = T(l_r_1_0, l_r_1_1)
            l_r = T(l_r_0, l_r_1)
            _r0 = l_r[0]
            _r1_0 = l_r[1][0]
            _r1_1 = l_r[1][1][1]
            _r1 = T(_r1_0, _r1_1)
            return T(_r0, _r1)
        else:
            return throw("p(main): query value does not conform to return type Tuple TBool (ListOf TBool)")
    
    # Generates a random sample of the main function
    def generate(self):
        s = (rand() < 0.5)
        _r0 = s
        if s:
            h1 = (rand() < 0.9)
        else:
            h1 = (rand() < 0.2)
        if s:
            h2 = (rand() < 0.9)
        else:
            h2 = (rand() < 0.2)
        if s:
            h3 = (rand() < 0.9)
        else:
            h3 = (rand() < 0.2)
        if s:
            h4 = (rand() < 0.9)
        else:
            h4 = (rand() < 0.2)
        if s:
            h5 = (rand() < 0.9)
        else:
            h5 = (rand() < 0.2)
        if s:
            h6 = (rand() < 0.9)
        else:
            h6 = (rand() < 0.2)
        if s:
            h7 = (rand() < 0.9)
        else:
            h7 = (rand() < 0.2)
        if s:
            h8 = (rand() < 0.9)
        else:
            h8 = (rand() < 0.2)
        if s:
            h9 = (rand() < 0.9)
        else:
            h9 = (rand() < 0.2)
        if s:
            h10 = (rand() < 0.9)
        else:
            h10 = (rand() < 0.2)
        if h10:
            _t18 = True
        elif s:
            _t18 = (rand() < 0.9)
        else:
            _t18 = (rand() < 0.2)
        _r1 = ConsInferenceList((True if ((rand() < 0.9) if s else (rand() < 0.2)) else h1), ConsInferenceList((h2 if h1 else False), ConsInferenceList((True if h2 else h3), ConsInferenceList((h4 if h3 else False), ConsInferenceList((True if h4 else h5), ConsInferenceList((h6 if h5 else False), ConsInferenceList((True if h6 else h7), ConsInferenceList((h8 if h7 else False), ConsInferenceList((True if h8 else h9), ConsInferenceList((h10 if h9 else False), ConsInferenceList(_t18, EmptyInferenceList())))))))))))
        return T(_r0, _r1)
    
    

# Example Initialization
main = Main()
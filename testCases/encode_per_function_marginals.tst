backends: interpreter
writeLogits_len[isRed](0.3)=2
writeLogits_at[isRed](0.3, indexOf(True))~=0.3
writeLogits_len[isBig](0.3)=2
writeLogits_at[isBig](0.3, indexOf(True))~=0.2
writeLogits_len[main](0.3)=4
writeLogits_at[main](0.3, indexOf(True))~=0.3
writeLogits_at[main](0.3, indexOf(False))~=0.7

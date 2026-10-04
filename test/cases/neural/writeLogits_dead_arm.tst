backends: interpreter, julia, python
writeLogits_len[main](True)=5
writeLogits_len[main](False)=5
writeLogits_len[side](True)=5
writeLogits_at[side](True, indexOf(Left True))~=1.0
writeLogits_at[side](True, indexOf(Left False))~=0.0
writeLogits_len[side](False)=5
writeLogits_at[side](False, indexOf(Right False))~=1.0
writeLogits_at[side](False, indexOf(Right True))~=0.0

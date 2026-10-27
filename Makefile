.PHONY: rocq clean

ROCQC=rocq compile

rocq:
	$(ROCQC) CompMap.v
	$(ROCQC) GDS_Language.v
	$(ROCQC) GDS_Testing.v
	$(ROCQC) Valuation.v
	$(ROCQC) GDS_Inductive.v

clean:
	rm -f *.vo* *.glob *.aux .*.aux .*.cache

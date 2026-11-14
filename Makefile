.PHONY: rocq clean

ROCQC=rocq compile

rocq:
	$(ROCQC) Valuation.v
	$(ROCQC) GDS_Inductive.v
	$(ROCQC) GDS_Solving.v
	$(ROCQC) GDS_Examples.v
	$(ROCQC) Type_System.v



clean:
	rm -f *.vo* *.glob *.aux .*.aux .*.cache

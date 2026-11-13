.PHONY: rocq clean

ROCQC=rocq compile

rocq:
	$(ROCQC) Valuation.v
	$(ROCQC) GDS_Inductive.v

clean:
	rm -f *.vo* *.glob *.aux .*.aux .*.cache


run: mkTop.exe
	./mkTop.exe -m 15

mkTop.exe: mkTop
	bsc -sim -e mkTop -o mkTop.exe bs_fp.c

BluespecFP.bsv bs_fp.c Floats.bs FloatsTypes.bs:
	runhaskell floating_point_issues.hs 

mkTop: BluespecFP.bsv bs_fp.c Floats.bs FloatsTypes.bs 
	bsc -sim -g mkTop -u Top.bs	
	
verilog: mkTop
	bsc -verilog -g mkFloatss -u Floats.bs

clean: 
	rm -rf *.ba *.bo BluespecFP.bsv *.c FloatsTypes.bs Floats.bs *.h *.o *.cxx *.exe *.so *.v obj_dir/

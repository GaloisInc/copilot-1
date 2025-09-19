run: mkTop.exe
	./mkTop.exe -m 15

mkTop.exe: mkTop
	bsc -sim -e mkTop -o mkTop.exe bs_fp.c

BluespecFP.bsv bs_fp.c Fibs.bs FibsTypes.bs:
	runhaskell fibs.hs 

mkTop: BluespecFP.bsv bs_fp.c Fibs.bs FibsTypes.bs
	bsc -sim -g mkTop -u Top.bs	
	
verilog: mkTop
	bsc -verilog -g mkFibs -u Fibs.bs

clean: 
	rm -rf *.ba *.bo BluespecFP.bsv *.c FibsTypes.bs Fibs.bs *.h *.o *.cxx *.exe *.so *.v obj_dir/

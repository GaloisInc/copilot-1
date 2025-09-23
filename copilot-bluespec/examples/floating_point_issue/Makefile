

BluespecFP.bsv bs_fp.c Floats.bs FloatsTypes.bs:
	runhaskell floating_point_issues.hs 

mkTop: BluespecFP.bsv bs_fp.c Floats.bs FloatsTypes.bs Top.bs
	bsc -sim -g mkTop -u Top.bs	
	
run: mkTop
	bsc -sim -e mkTop -o mkTop.exe bs_fp.c

clean: 
	rm *.ba *.bo

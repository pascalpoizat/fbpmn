
all :
	@echo 'I see no all here. Try compile, clean, nonregression-build, nonregression-check.'

compile : RunAlloy.class RunAlloyAll.class

RunAlloy.class : RunAlloy.java org.alloytools.alloy.dist.jar
	javac -cp org.alloytools.alloy.dist.jar RunAlloy.java

RunAlloyAll.class : RunAlloyAll.java org.alloytools.alloy.dist.jar
	javac -cp org.alloytools.alloy.dist.jar RunAlloyAll.java

clean :
	rm -f RunAlloyAll.class RunAlloy.class

runall :
	java -cp .:org.alloytools.alloy.dist.jar RunAlloyAll example1_check.als

run1 :
	java -cp .:org.alloytools.alloy.dist.jar RunAlloy example1_check.als 'check$$1'

# explicitely list the validated tests
NONREGRESSIONTESTS=example1 example2 example3 example4 example5 example6 example7 example8 example9 example10

nonregression-build :
	java -cp .:org.alloytools.alloy.dist.jar RunAlloyAll $(addsuffix _check.als,$(NONREGRESSIONTESTS)) >nonregression.out

nonregression-check :
	java -cp .:org.alloytools.alloy.dist.jar RunAlloyAll $(addsuffix _check.als,$(NONREGRESSIONTESTS)) >/tmp/nonregression.out
	diff -u2 /tmp/nonregression.out nonregression.out

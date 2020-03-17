
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
	java -cp .:org.alloytools.alloy.dist.jar RunAlloyAll example1.als

run1 :
	java -cp .:org.alloytools.alloy.dist.jar RunAlloy example1.als 'check$$1'

# explicitely list the validated tests
NONREGRESSIONTESTS=example1.als example2.als example3.als example4.als example5.als example6.als example7.als

nonregression-build :
	java -cp .:org.alloytools.alloy.dist.jar RunAlloyAll $(NONREGRESSIONTESTS) >nonregression.out

nonregression-check :
	java -cp .:org.alloytools.alloy.dist.jar RunAlloyAll $(NONREGRESSIONTESTS) >/tmp/nonregression.out
	diff -u2 /tmp/nonregression.out nonregression.out

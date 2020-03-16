
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

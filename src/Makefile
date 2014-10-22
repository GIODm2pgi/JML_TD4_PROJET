JMLC = jmlc -O -Q
RM = rm
JAVA = java
JAVAC = javac
JUNIT4 = ../lib/junit4-4.8.2.jar
JMLRUNTIME = /usr/local/JML/bin/jmlruntime.jar
JMLCLASSPATH = .:$(JMLRUNTIME)
JMLJUNITCLASSPATH = $(JMLCLASSPATH):$(JUNIT4)

run : ExplosivesMain.class
	$(JAVA) -cp $(JMLCLASSPATH) ExplosivesMain

Explosives.class : Explosives.java
	$(JMLC) Explosives.java

ExplosivesMain.class : Explosives.class ExplosivesMain.java
	$(JAVAC) ExplosivesMain.java

TestExplosivesJUnit4.class : Explosives.class TestExplosivesJUnit4.java
	$(JAVAC) -classpath $(JMLJUNITCLASSPATH)  TestExplosivesJUnit4.java

TestExplosivesJUnit4.run : TestExplosivesJUnit4.class
	 java -cp $(JMLJUNITCLASSPATH) TestExplosivesJUnit4

TestExplosivesJUnit4Public.class : Explosives.class TestExplosivesJUnit4Public.java
	$(JAVAC) -classpath $(JMLJUNITCLASSPATH)  TestExplosivesJUnit4Public.java

TestExplosivesJUnit4Public.run : TestExplosivesJUnit4Public.class
	 java -cp $(JMLJUNITCLASSPATH) TestExplosivesJUnit4Public

TestExplosivesJUnit4FindBat.class : Explosives.class TestExplosivesJUnit4FindBat.java
	$(JAVAC) -classpath $(JMLJUNITCLASSPATH)  TestExplosivesJUnit4FindBat.java

TestExplosivesJUnit4FindBat.run : TestExplosivesJUnit4FindBat.class
	 java -cp $(JMLJUNITCLASSPATH) TestExplosivesJUnit4FindBat
	 
TestExplosivesJUnit4FindBatVSFindBatSimple.class : Explosives.class TestExplosivesJUnit4FindBatVSFindBatSimple.java
	$(JAVAC) -classpath $(JMLJUNITCLASSPATH)  TestExplosivesJUnit4FindBatVSFindBatSimple.java

TestExplosivesJUnit4FindBatVSFindBatSimple.run : TestExplosivesJUnit4FindBatVSFindBatSimple.class
	 java -cp $(JMLJUNITCLASSPATH) TestExplosivesJUnit4FindBatVSFindBatSimple

eclipseBin :
	cp *.class ../bin

clean : 
	$(RM) *.class


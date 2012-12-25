#SRCS = AAF.java Argument.java Defeat.java Test.java
SRCS = PAFTest.java Plot.java
OBJS = $(subst .java,.class,$(SRCS))

%.class: %.java
	javac -cp /usr/share/java/jfreechart.jar $<

sim: PAFTest.class
	java -Xmx256m -Xms256m -verbose:gc -cp . PAFTest

plot: Plot.class
	java -cp .:/usr/share/java/jfreechart.jar Plot
	eog plot.png

.PHONY: sim plot
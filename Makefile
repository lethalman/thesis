#SRCS = AAF.java Argument.java Defeat.java Test.java
SRCS = PAFTest.java Structures.java Generator.java Instance.java Semantics.java Montecarlo.java
OBJS = $(subst .java,.class,$(SRCS))

.stamp: $(SRCS)
	javac -cp /usr/share/java/jfreechart.jar $(SRCS)
	touch .stamp

$(OBJS): .stamp

run: PAFTest.class $(OBJS)
	java -Xmx256m -Xms256m -verbose:gc -cp . PAFTest

plot: Plot.class
	java -cp .:/usr/share/java/jfreechart.jar Plot
	eog plot.png

.PHONY: run plot
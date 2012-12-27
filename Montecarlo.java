import java.util.*;
import java.lang.reflect.*;

class Rational {
    public int num;
    public int den;

    public Rational (int num, int den) {
	this.num = num;
	this.den = den;
    }

    public double toDouble () {
        return num/(double)den;
    }

    public String toString () {
	return num+"/"+den+"="+(num/(double)den);
    }
}

class Stats {
    double meanTime;
    double meanSuccesses, meanTrials;
    double meanValue, meanConditional;
    double absError, relError;
    double maxValue, minValue=1000000000;

    public static String headerString (String prefix) {
	return prefix+"CPU time,"+prefix+"Successes,"+prefix+"Trials,"+prefix+"Mean Conditional,"+prefix+"Mean Value,"+prefix+"Abs Error,"+prefix+"Rel Error,"+prefix+"Min Value,"+prefix+"Max Value";
    }

    public String toString () {
	return meanTime+","+meanSuccesses+","+meanTrials+","+meanConditional+","+meanValue+","+absError+","+relError+","+minValue+","+maxValue;
    }
}

abstract class Montecarlo {
    Stats runs (Semantics semantic, PAF paf, ArgSet set, int runs) {
        Stats stats = new Stats ();
        for (int i=0; i < runs; i++) {
            System.out.println ("Run "+i);
            long start = System.currentTimeMillis ();
            Rational r = run (semantic, paf, set);
            stats.meanTime += System.currentTimeMillis ()-start;
            double value = semantic.conditional(paf, set)*r.toDouble ();
            stats.maxValue = Math.max (stats.maxValue, value);
            stats.minValue = Math.min (stats.minValue, value);
            stats.meanValue += value;
	    stats.meanConditional += r.toDouble();
	    stats.meanSuccesses += r.num;
            stats.meanTrials += r.den;
        }
        stats.meanTime /= runs;
        stats.meanValue /= runs;
	stats.meanConditional /= runs;
	stats.meanSuccesses /= runs;
        stats.meanTrials /= runs;
        stats.absError = (stats.maxValue-stats.minValue)/2;
        stats.relError = stats.absError / stats.meanValue;
        return stats;
    }

    abstract Rational run (Semantics semantic, PAF paf, ArgSet set);

    static Montecarlo fromString (String s) {
	try {
	    String[] v = s.split (" ");
	    ArrayList<String> trimmed = new ArrayList<String> ();
	    for (String e: v) {
		if (e.trim().length() > 0) {
		    trimmed.add (e.trim ());
		}
	    }
	    Class c = Class.forName (trimmed.get(0));
	    Constructor ctor = c.getDeclaredConstructors()[0];
	    Double[] args = new Double[trimmed.size()-1];
	    for (int i=1; i < trimmed.size(); i++) {
		args[i-1] = Double.parseDouble (trimmed.get(i));
	    }
	    return (Montecarlo) ctor.newInstance ((Object[]) args);
	} catch (Exception e) {
	    throw new RuntimeException (e);
	}
    }
}

// perform N iterations for montecarlo
class MontecarloIter extends Montecarlo {
    int N;

    public MontecarloIter (int N) {
        this.N = N;
    }

    @Override
    public Rational run (Semantics semantic, PAF paf, ArgSet set) {
	int X = 0;
	for (int i=0; i < N; i++) {
	    DAF daf = semantic.montecarloSample (paf, set);
	    if (semantic.evaluate (daf, set)) {
                X++;
	    }
	}

	return new Rational (X, N);
    }
}

class MontecarloError extends Montecarlo {
    double quantile;
    double error;

    public MontecarloError (double quantile, double error) {
        this.quantile = quantile;
        this.error = error;
    }

    // 1-a/2 quantile (95% -> 1.96)
    @Override
    public Rational run (Semantics semantic, PAF paf, ArgSet set) {
	int N = 0;
	int X = 0;
	double Nthreshold;
	double cond = semantic.conditional (paf, set);
        double z2 = quantile*quantile;
        double e2 = error*error;
        double c2 = cond*cond;
	do {
            DAF daf = semantic.montecarloSample (paf, set);
	    if (semantic.evaluate (daf, set)) {
		X++;
	    }
	    N++;

	    // Agresti-Coull interval
	    double n = N+z2;
	    double p = (X+(z2/2))/n;
	    Nthreshold = ((p*(1-p))/e2)*z2*c2-z2;
	} while (N <= Nthreshold);

	return new Rational (X, N);
    }
}

class MontecarloTimed extends Montecarlo {
    class Task extends TimerTask {
        volatile boolean terminated = false;

        @Override
        public void run () {
            terminated = true;
        }
    }

    long milliseconds;

    public MontecarloTimed (long milliseconds) {
        this.milliseconds = milliseconds;
    }

    @Override
    public Rational run (Semantics semantic, PAF paf, ArgSet set) {
        Timer t = new Timer (true);
        Task task = new Task ();
        t.schedule (task, milliseconds);

	int X = 0;
        int N = 0;
        while (!task.terminated) {
	    DAF daf = semantic.montecarloSample (paf, set);
	    if (semantic.evaluate (daf, set)) {
                X++;
	    }
            N++;
	}

	return new Rational (X, N);        
    }
}

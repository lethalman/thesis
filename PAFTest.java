import java.util.*;
import java.io.*;

class ArgSet extends HashSet<String> {
    public ArgSet (ArgSet set) {
	super (set);
    }

    public ArgSet (String ... args) {
	for (String n: args) {
	    this.add (n);
	}
    }

    public String toString () {
	StringBuilder b = new StringBuilder();
	for (String a: this) {
	    b.append (a);
	    b.append (" ");
	}
	return b.toString();
    }
}

class ArgProb extends HashMap<String,Double> {
}

class Defeat {
    public String a;
    public String b;

    public Defeat (String a, String b) {
	this.a = a;
	this.b = b;
    }

    public String toString () {
	return "("+a+","+b+")";
    }
}

class DefeatSet extends HashSet<Defeat> {
    public String toString () {
	StringBuilder b = new StringBuilder ();
	for (Defeat d: this) {
	    b.append (d);
	    b.append (" ");
	}
	return b.toString();
    }
}

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

abstract class Semantics {
    public abstract boolean evaluate (DAF daf, ArgSet set);

    public DAF montecarloSample (PAF paf, ArgSet set) {
        DAF daf;
        do {
            daf = new DAF();
	    for (String a: paf.argsList) {
		if (paf.args.get(a) >= Math.random()) {
		    daf.addArg (a);
		}
	    }
            for (String a: daf.args) {
		for (String b: paf.getDefeats(a).keySet()) {
		    if (daf.args.contains (b) && paf.defeats.get(a).get(b) >= Math.random ()) {
			daf.addDefeat (a, b);
		    }
                }
            }
        } while (filterSample (daf, set));
        return daf;
    }

    public boolean filterSample (DAF daf, ArgSet set) {
        return false; // don't filter by default
    }

    public double conditional (PAF paf, ArgSet set) {
	return 1;
    }
}


class ConflictFreeSemantics extends Semantics {
    @Override
    public boolean evaluate (DAF daf, ArgSet set) {
	return daf.conflictFree (set);
    }
}

class AdmissibleSemantics extends Semantics {
    @Override
    public boolean evaluate (DAF daf, ArgSet set) {
	return daf.admissible (set);
    }
}

class StableSemantics extends Semantics {
    @Override
    public boolean evaluate (DAF daf, ArgSet set) {
	return daf.stable (set);
    }
}

class CompleteSemantics extends Semantics {
    @Override
    public boolean evaluate (DAF daf, ArgSet set) {
	return daf.complete (set);
    }
}

class PreferredSemantics extends Semantics {
    @Override
    public boolean evaluate (DAF daf, ArgSet set) {
	return daf.preferred (set);
    }
}

class GroundedSemantics extends Semantics {
    @Override
    public boolean evaluate (DAF daf, ArgSet set) {
	return daf.grounded (set);
    }
}

abstract class GivenConflictFreeSemantics extends Semantics {
    @Override
    public DAF montecarloSample (PAF paf, ArgSet set) {
        DAF daf;
	do {
	    daf = new DAF();
	    for (String a: set) {
		// args must be in daf for set to be conflict-free
		daf.addArg (a);
	    }
	    for (String a: paf.argsList) {
                double r = Math.random();
		if (!set.contains(a) && paf.args.get(a) >= r) {
		    daf.addArg (a);
		}
	    }
	    for (String a: daf.args) {
		for (String b: paf.getDefeats(a).keySet()) {
		    if (set.contains(a) && set.contains(b)) {
			// conflict
			continue;
		    }
		    if (daf.args.contains (b) && paf.defeats.get(a).get(b) >= Math.random ()) {
			daf.addDefeat (a, b);
		    }
		}
	    }
	} while (filterSample (daf, set));
        return daf;
    }

    @Override
    public double conditional (PAF paf, ArgSet set) {
	return paf.conflictFree (set);
    }
}

abstract class GivenAdmissibleSemantics1 extends Semantics {
    @Override
    public DAF montecarloSample (PAF paf, ArgSet set) {
        DAF daf;
	do {
	    daf = new DAF();
	    for (String a: set) {
		// args must be in daf for set to be admissible
		daf.addArg (a);
	    }
	    for (String a: paf.argsList) {
		if (!set.contains(a) && Math.random () <= paf.args.get(a)) {
		    daf.addArg (a);
		}
	    }
	    for (String a: daf.args) {
		for (String b: paf.getDefeats(a).keySet()) {
		    if (set.contains(a) && set.contains(b)) {
			// conflict
			continue;
		    }
		    if (set.contains (b)) {
			// can't be handled here because it would be incorrect, do it later
			continue;
		    }
		    if (daf.args.contains (b) && Math.random () <= paf.defeats.get(a).get(b)) {
			daf.addDefeat (a, b);
		    }
		}
	    }
	    for (String a: set) {
		for (String b: paf.getDefeatedBy(a).keySet()) {
		    if (daf.args.contains (b) && !set.contains (b)) {
			// "a" must be defended from "b"
			boolean defended = false;
			for (String c: daf.getDefeatedBy(b)) {
			    if (set.contains (c)) {
				defended = true;
				break;
			    }
			}
			if (!defended) {
			    // not acceptable
			    continue;
			}
			if (Math.random() <= paf.defeats.get(b).get(a)) {
			    daf.addDefeat (b, a);
			}
		    }
		}
	    }
	} while (filterSample (daf, set));
        return daf;
    }

    @Override
    public double conditional (PAF paf, ArgSet set) {
	return paf.admissible (set);
    }
}

abstract class GivenAdmissibleSemantics extends Semantics {
    @Override
    public DAF montecarloSample (PAF paf, ArgSet set) {
        DAF daf;
	do {
	    daf = new DAF();
	    for (String a: set) {
		// args must be in daf for set to be admissible
		daf.addArg (a);
	    }
	    for (String a: paf.argsList) {
		if (!set.contains(a) && Math.random () <= paf.args.get(a)) {
		    daf.addArg (a);
		}
	    }
	    // first generate defeats toward S
	    for (String a: set) {
		for (String b: paf.getDefeatedBy(a).keySet()) {
		    if (set.contains (b)) {
			// conflict
			continue;
		    }
		    if (daf.args.contains (b) && Math.random() <= paf.defeats.get(b).get(a)) {
			daf.addDefeat (b, a);
			// generate defenders
			for (String c: paf.getDefeatedBy(b).keySet()) {
			    daf.addDefeat (c, b);
			}
		    }
		}
	    }
	    // generate everything else, if a node in S is attacked then generate a defender
	    for (String a: daf.args) {
		for (String b: paf.getDefeats(a).keySet()) {
		    if (set.contains(a) && set.contains(b)) {
			// conflict
			continue;
		    }
		    if (set.contains(b)) {
			// already considered
			continue;
		    }
		    if (daf.args.contains (b) && !daf.getDefeats(a).contains(b) && Math.random () <= paf.defeats.get(a).get(b)) {
			daf.addDefeat (a, b);
		    }
		}
	    }
	} while (filterSample (daf, set));
        return daf;
    }

    @Override
    public double conditional (PAF paf, ArgSet set) {
	return paf.admissible (set);
    }
}

class CompleteGivenConflictFreeSemantics extends GivenConflictFreeSemantics {
    @Override
    public boolean evaluate (DAF daf, ArgSet set) {
	return daf.completeGivenConflictFree (set);
    }
}

class CompleteGivenAdmissibleSemantics extends GivenAdmissibleSemantics {
    @Override
    public boolean evaluate (DAF daf, ArgSet set) {
	return daf.completeGivenAdmissible (set);
    }
}


class PreferredGivenConflictFreeSemantics extends GivenConflictFreeSemantics {
    @Override
    public boolean evaluate (DAF daf, ArgSet set) {
	return daf.preferredGivenConflictFree (set);
    }
}

class PreferredGivenAdmissibleSemantics extends GivenAdmissibleSemantics {
    @Override
    public boolean evaluate (DAF daf, ArgSet set) {
	return daf.preferredGivenAdmissible (set);
    }
}

class GroundedGivenConflictFreeSemantics extends GivenConflictFreeSemantics {
    @Override
    public boolean evaluate (DAF daf, ArgSet set) {
	return daf.groundedGivenConflictFree (set);
    }
}

class GroundedGivenAdmissibleSemantics extends GivenAdmissibleSemantics {
    @Override
    public boolean evaluate (DAF daf, ArgSet set) {
	return daf.groundedGivenAdmissible (set);
    }
}

class Range {
    double a;
    double b;

    public Range (double a, double b) {
        this.a = a;
        this.b = b;
    }

    boolean has (double v) {
        return v > a && v <= b;
    }
}

class Distribution extends ArrayList<Distribution.Entry> {
    class Entry {
        double value;
        double prob;

        public Entry (double value, double prob) {
            this.value = value;
            this.prob = prob;
        }
    }

    public void add (double value, double prob) {
        add (new Entry (value, prob));
    }

    public double sample () {
        double r = Math.random();
        double c = 0;
        for (Entry e: this) {
            c += e.prob;
            if (r <= c) {
                return e.value;
            }
        }
        throw new RuntimeException ("Wrong distribution");
    }
}

class Generator {
    int nargs;
    Distribution nodeProb;
    Distribution numdefProb;
    Distribution defProb;

    public Generator (int nargs, Distribution nodeProb, Distribution numdefProb, Distribution defProb) {
        this.nargs = nargs;
        this.nodeProb = nodeProb;
        this.numdefProb = numdefProb;
        this.defProb = defProb;
    }

    public Instance generateInstance () {
	PAF paf = new PAF();
        // gen args
        int argsGenerated = 0;
        argsGenerated:
        for (char a='a'; a <= 'z'; a++) {
            paf.addArg(""+a, nodeProb.sample ());
            argsGenerated++;
            if (argsGenerated == nargs) {
                break argsGenerated;
            }
        }
        if (argsGenerated < nargs) {
            throw new RuntimeException ("argsGenerated < nargs");
        }
	// gen possible S 
	ArgSet s = new ArgSet();
	for (int i=0; i <= paf.argsList.size()/2; i++) {
	    s.add (paf.argsList.get (i));
	}
	System.out.println (s);
        // gen defeats, no defeats within S
        for (String a: paf.argsList) {
            int numdef = (int)numdefProb.sample ();
            for (int i=0; i < numdef; i++) {
                String b;
                do {
                    int j = (int) (Math.random()*nargs);
                    b = paf.argsList.get(j);
                } while ((s.contains(a) && s.contains(b)) || paf.getDefeats(a).get(b) != null); // FIXME
		paf.addDefeat (a, b, 0);
            }
        }
        return paf;
    }

    public PAF generateTree () {
        PAF paf = new PAF();
        // gen args
        int argsGenerated = 0;
        argsGenerated:
        for (char a='a'; a <= 'z'; a++) {
            paf.addArg(""+a, nodeProb.sample ());
            argsGenerated++;
            if (argsGenerated == nargs) {
                break argsGenerated;
            }
        }
        if (argsGenerated < nargs) {
            throw new RuntimeException ("argsGenerated < nargs");
        }
        // gen defeats
        for (String a: paf.argsList) {
            int numdef = (int)numdefProb.sample ();
            for (int i=0; i < numdef; i++) {
                String b;
                do {
                    int j = (int) (Math.random()*nargs);
                    b = paf.argsList.get(j);
                } while (paf.getDefeats(a).get(b) != null); // FIXME
		paf.addDefeat (a, b, defProb.sample ());
            }
        }
        return paf;
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
    Stats runs (PAF paf, Semantics semantic, ArgSet set, int runs) {
        Stats stats = new Stats ();
        for (int i=0; i < runs; i++) {
            System.out.println ("Run "+i);
            long start = System.currentTimeMillis ();
            Rational r = run (paf, semantic, set);
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

    abstract Rational run (PAF paf, Semantics semantic, ArgSet set);
}

// perform N iterations for montecarlo
class MontecarloIter extends Montecarlo {
    int N;

    public MontecarloIter (int N) {
        this.N = N;
    }

    @Override
    public Rational run (PAF paf, Semantics semantic, ArgSet set) {
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
    public Rational run (PAF paf, Semantics semantic, ArgSet set) {
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
	    double p = (X+(z2/2))/n*cond;
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
    public Rational run (PAF paf, Semantics semantic, ArgSet set) {
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

class PAF {
    public ArgProb args = new ArgProb ();
    public HashMap<String,ArgProb> defeats = new HashMap<String,ArgProb>();
    public HashMap<String,ArgProb> defeatedBy = new HashMap<String,ArgProb>();

    ArrayList<String> argsList = new ArrayList<String>();
    ArrayList<Defeat> defeatsList = new ArrayList<Defeat>();
    static ArgProb emptyMap = new ArgProb();

    public void addArg (String name, double prob) {
	args.put (name, prob);
	argsList.add (name);
    }

    public void addArgs (Object ... objs) {
	for (int i=0; i < objs.length; i += 2) {
	    addArg ((String) objs[i], (Double) objs[i+1]);
	}
    }

    public void addDefeat (String a, String b, double prob) {
	ArgProb out = defeats.get(a);
	if (out == null) {
	    out = new ArgProb();
	    defeats.put (a, out);
	}
	out.put (b, prob);

	ArgProb in = defeatedBy.get(b);
	if (in == null) {
	    in = new ArgProb();
	    defeatedBy.put (b, in);
	}
	in.put (a, prob);

	defeatsList.add (new Defeat (a, b));
    }

    public void addDefeats (Object ... objs) {
	for (int i=0; i < objs.length; i+=3) {
	    addDefeat ((String) objs[i], (String) objs[i+1], (Double) objs[i+2]);
	}
    }

    public void setArg (String a, double p) {
	args.put (a, p);
    }

    public void setDefeat (String a, String b, double p) {
	defeats.get(a).put(b, p);
	defeatedBy.get(b).put(a, p);
    }

    public ArgProb getDefeats (String a) {
	ArgProb defs = defeats.get (a);
	if (defs == null) {
	    return emptyMap;
	}
	return defs;
    }

    public ArgProb getDefeatedBy (String a) {
	ArgProb defs = defeatedBy.get (a);
	if (defs == null) {
	    return emptyMap;
	}
	return defs;
    }

    // FIND SETS

    public ArgSet findPossibleSetGood (Semantics semantic, int samples) {
        ArgSet maxset = new ArgSet();
        double maxprob1 = 0;
        double maxprob2 = 0;
        Montecarlo m = new MontecarloError (1.96, 0.001);
        for (int i=0; i < samples; i++) {
            ArgSet set = new ArgSet();
	    while (set.size() < args.size()/2) {
		for (String a: argsList) {
		    if (Math.random() > 0.5) {
			set.add (a);
		    }
		}
	    }
	    double cond = semantic.conditional (this, set);
	    if (cond > maxprob2) {
		double p = cond*m.run(this, semantic, set).toDouble ();
		if (p > maxprob1) {
		    maxset = set;
		    maxprob1 = p;
		    maxprob2 = cond;
		}
	    }
        }
        return maxset;
    }

    public ArgSet findPossibleSetHill (Semantics semantic, int samples) {
        ArgSet maxset = new ArgSet();
        double maxprob1 = 0;
        double maxprob2 = 0;
        Montecarlo m = new MontecarloIter (1000);
	List<ArgSet> cfsets = new ArrayList<ArgSet> ();
        for (int i=0; i < samples; i++) {
            ArgSet set = new ArgSet();
	    //while (set.size() < args.size()/2) {
	    for (String a: argsList) {
		if (args.get(a) == 1) {
		    set.add (a);
		} else if (Math.random() > 0.5) {
		    set.add (a);
		}
	    }
	    //}
	    double cond = semantic.conditional(this, set);
	    if (cond > 0.6 && cond < 1) {
		cfsets.add (set);
	    }
        }
	// hill climbing
	return hillClimbing (semantic, cfsets);
    }

    public ArgSet findPossibleSet (Semantics semantic) {
	PrintWriter pw = null;
	try {
	    pw = new PrintWriter (new FileOutputStream ("genset.mod"), true);
	} catch (IOException e) {
            e.printStackTrace ();
	}
	pw.print ("set N := {");
	for (int i=0; i < argsList.size(); i++) {
	    pw.print ("'"+argsList.get(i)+"'");
	    if (i < argsList.size()-1) {
		pw.print (", ");
	    }
	}
	pw.print ("};\n");
	pw.print ("var x{N} binary;\n"+
		  "var s{N} binary;\n"+
		  "param p{N} > 0, <= 1;\n"+
		  "param def{N, N} >= 0, < 1;\n"+
		  "maximize cost: sum{i in N} s[i]*p[i] + sum{i in N, j in N} -3*s[i]*def[j,i]*p[j] + sum{i in N} -(1-s[i])*p[i];\n"+
		  "certain{i in N: p[i]=1.0}: s[i] = 1;\n"+
		  "solve;\n"+
		  "printf{i in N: s[i]}: '%s ', i;\n"+
		  "printf '\\n';\n"+
		  "data;\n");
	pw.print ("param p := ");
	for (int i=0; i < argsList.size(); i++) {
	    String a = argsList.get(i);
	    pw.print ("["+a+"] "+args.get(a));
	    if (i < argsList.size()-1) {
		pw.print (", ");
	    }
	}
	pw.print (";\n");
	pw.print ("param def : ");
	for (String a: argsList) {
	    pw.print ("'"+a+"' ");
	}
	pw.print (":=\n");
	for (String a: argsList) {
	    pw.print ("'"+a+"' ");
	    for (String b: argsList) {
		double p = getDefeats(a).get(b) != null ? getDefeats(a).get(b) : 0;
		pw.print (p+" ");
	    }
	    pw.print ("\n");
	}
	pw.print (";");
	pw.close ();
	try {
	    Runtime.getRuntime().exec ("glpsol --model genset.mod --display out").waitFor ();
	    BufferedReader r = new BufferedReader (new FileReader ("out"));
	    String line = r.readLine ();
	    ArgSet s = new ArgSet();
	    for (String a: line.split(" ")) {
		s.add (a.trim());
	    }
	    ArrayList<ArgSet> l = new ArrayList<ArgSet> ();
	    l.add (s);
	    return hillClimbing (semantic, l);
	} catch (Exception e) {
	    e.printStackTrace ();
	}
	return new ArgSet();
    }

    ArgSet hillClimbing (Semantics semantic, Collection<ArgSet> cfsets) {
	ArgSet best = new ArgSet();
	double pbest = 0;
        Montecarlo m = new MontecarloIter (3000);
	for (ArgSet s: cfsets) {
	    System.out.println ("Hill from "+s);
	    ArgSet cur = s;
	    double ccur = semantic.conditional(this, cur);
	    double pcur = ccur*m.run(this, semantic, cur).toDouble();
	    while (true) {
		ArgSet next = null;
		double cnext = ccur;
		double pnext = pcur;
		for (String a: argsList) {
		    if (!cur.contains (a)) {
			cur.add (a);
			double c = semantic.conditional(this, cur);
			if ((cnext < 0.6 && c > cnext) || (c >= 0.6 && c < 1)) {
			    double p = c*m.run(this, semantic, cur).toDouble();
			    if (cnext < 0.6 || p > pnext) {
				next = new ArgSet (cur);
				cnext = c;
				pnext = p;
			    }
			}
			cur.remove (a);
		    } else if (args.get(a) < 1) {
			// remove
			cur.remove (a);
			double c = semantic.conditional(this, cur);
			if (cnext < 0.6 || pnext == 0) {
			    double p = c*m.run(this, semantic, cur).toDouble();
			    if (p > pnext) {
				next = new ArgSet (cur);
				cnext = c;
				pnext = p;
			    }
			}
			// substitute
			for (String b: argsList) {
			    if (!cur.contains (b)) {
				cur.add (b);
				c = semantic.conditional(this, cur);
				if ((cnext < 0.6 && c > cnext) || (c >= 0.6 && c < 1)) {
				    double p = c*m.run(this, semantic, cur).toDouble();
				    if (cnext < 0.6 || p > pnext) {
					next = new ArgSet (cur);
					cnext = c;
					pnext = p;
				    }
				}
				cur.remove (b);
			    }
			}
			cur.add (a);
		    }
		}
		if (next == null) {
		    break;
		}
		cur = next;
		ccur = cnext;
		pcur = pnext;
		System.out.println (cur+" "+ccur+" "+pcur);
	    }
	    if (pcur > pbest) {
		best = cur;
		pbest = pcur;
	    }
	}
        return best;
    }

    // SEMANTIC

    public double conflictFree (ArgSet set) {
        double p1 = 1; // set contained in args
        for (String a: set) {
            p1 *= args.get(a);
        }
        double p2 = 1; // no conflicts
        for (String b: set) {
            for (String c: set) {
                Double p = getDefeats(b).get(c);
                if (p != null) {
                    p2 *= 1-(double)p;
                }
            }
        }
        return p1*p2;
    }

    public double admissible (ArgSet set) {
        double p3 = 1;
        for (String d: argsList) {
            if (!set.contains (d)) {
                double p31 = 1-args.get(d);
                double p32 = 1;
                for (String e: getDefeats(d).keySet()) {
                    if (set.contains (e)) {
                        p32 *= 1-defeats.get(d).get(e);
                    }
                }
                p32 *= args.get(d);
                double p33;
                double p331 = 1;
                for (String f: getDefeats(d).keySet()) {
                    if (set.contains (f)) {
                        p331 *= 1-defeats.get(d).get(f);
                    }
                }
                double p332 = 1;
                for (String g: getDefeatedBy(d).keySet()) {
                    if (set.contains (g)) {
                        p332 *= 1-defeats.get(g).get(d);
                    }
                }
                p33 = args.get(d)*(1-p331)*(1-p332);
                p3 *= p31+p32+p33;
            }
        }
        return conflictFree(set)*p3;
    }

    // maybe wrong
    public double stable (ArgSet set) {
        double p3 = 1;
        for (String d: argsList) {
            if (!set.contains (d)) {
                double p31 = 1-args.get(d);
                double p32 = 1;
                for (String e: getDefeats(d).keySet()) {
                    if (set.contains (e)) {
                        p32 *= 1-defeats.get(d).get(e);
                    }
                }
                p32 *= args.get(d);
                p3 *= p31+p32;
                System.out.println(p3+" "+p31+" "+p32);
            }
        }
        return conflictFree(set)*p3;
    }

    // if semantic(world,set) == true then return P(world), 0 otherwise
    public double evaluateWorld (Semantics semantic, ArgSet set, ArgSet curArgs, DefeatSet curDefeats) {
	DAF daf = new DAF();
	double interp = 1;
	for (String arg: curArgs) {
	    daf.addArg (arg);
	    interp *= args.get(arg);
	}
	for (String arg: argsList) {
	    if (!curArgs.contains (arg)) {
		interp *= 1-args.get(arg);
	    }
	}
	for (Defeat d: curDefeats) {
	    daf.addDefeat (d.a, d.b);
	    interp *= defeats.get(d.a).get(d.b);
	}
	for (Defeat d: defeatsList) {
	    if (curArgs.contains (d.a) && curArgs.contains (d.b) && !curDefeats.contains (d)) {
		interp *= 1-defeats.get(d.a).get(d.b);
	    }
	}
	double ret = 0;
	if (interp != 0 && semantic.evaluate (daf, set)) {
	    ret = interp;
	    //System.out.println(interp+" "+daf);
	}
	return ret;
    }

    private double depthFirstHelperDefeat (Semantics semantic, ArgSet set, ArgSet curArgs, DefeatSet curDefeats, Defeat curDefeat) {
	double sum = evaluateWorld (semantic, set, curArgs, curDefeats);
	int idx = curDefeat == null ? -1 : defeatsList.indexOf (curDefeat);
	for (int i=idx+1; i < defeatsList.size(); i++) {
	    Defeat newDefeat = defeatsList.get (i);
	    if (!curArgs.contains (newDefeat.a) || !curArgs.contains (newDefeat.b)) {
		// invalid defeat
		continue;
	    }
	    if (set.contains (newDefeat.a) && set.contains (newDefeat.b)) {
		// conflict
		continue;
	    }
	    curDefeats.add (newDefeat);
	    sum += depthFirstHelperDefeat (semantic, set, curArgs, curDefeats, newDefeat);
	    curDefeats.remove (newDefeat);
	}
	return sum;
    }

    private double depthFirstHelperArg (Semantics semantic, ArgSet set, ArgSet curArgs, String curArg) {
	double sum = depthFirstHelperDefeat (semantic, set, curArgs, new DefeatSet(), null);
	int idx = curArg == null ? -1 : argsList.indexOf (curArg);
	for (int i=idx+1; i < argsList.size(); i++) {
	    String newArg = argsList.get (i);
            if (curArgs.contains (newArg)) {
                continue;
            }
	    curArgs.add (newArg);
	    sum += depthFirstHelperArg (semantic, set, curArgs, newArg);
	    curArgs.remove (newArg);
	}
	return sum;
    }

    // IMPORTANT: assumes conflict free
    public double depthFirst (Semantics semantic, ArgSet set) {
	return depthFirstHelperArg (semantic, set, new ArgSet(set), null) / semantic.conditional (this, set);
    }

    public String toString () {
        StringBuilder b = new StringBuilder();
        for (String a: argsList) {
            b.append (a+","+args.get(a)+" ");
        }
        b.append ("\n");
        for (Defeat d: defeatsList) {
            b.append (d.a+","+d.b+","+defeats.get(d.a).get(d.b)+" ");
        }
        return b.toString ();
    }
}

class DAF {
    public ArgSet args = new ArgSet();
    public HashMap<String,ArgSet> defeats = new HashMap<String,ArgSet>();
    public HashMap<String,ArgSet> defeatedBy = new HashMap<String,ArgSet>();
    public static ArgSet emptySet = new ArgSet ();

    ArrayList<String> argsList = new ArrayList<String> ();

    public void addArg (String name) {
	args.add (name);
	argsList.add (name);
    }

    public void addArgs (String ... names) {
	for (String n: names) {
	    addArg (n);
	}
    }

    public void addDefeat (String a, String b) {
	ArgSet out = defeats.get(a);
	if (out == null) {
	    out = new ArgSet();
	    defeats.put (a, out);
	}
	out.add (b);

	ArgSet in = defeatedBy.get(b);
	if (in == null) {
	    in = new ArgSet();
	    defeatedBy.put (b, in);
	}
	in.add (a);
    }

    public void addDefeats (String ... defs) {
	for (int i=0; i < defs.length; i += 2) {
	    addDefeat (defs[i], defs[i+1]);
	}
    }

    public ArgSet getDefeats (String a) {
	ArgSet defs = defeats.get (a);
	if (defs == null) {
	    return emptySet;
	}
	return defs;
    }

    public ArgSet getDefeatedBy (String a) {
	ArgSet defby = defeatedBy.get (a);
	if (defby == null) {
	    return emptySet;
	}
	return defby;
    }

    public boolean acceptable (ArgSet set, String a) {
	for (String b: getDefeatedBy(a)) {
	    boolean defended = false;
	    for (String c: getDefeatedBy(b)) {
		if (set.contains (c)) {
		    defended = true;
		    break;
		}
	    }
	    if (!defended) {
		return false;
	    }
	}
	return true;
    }

    public boolean hasArgSet (ArgSet set) {
	return args.containsAll (set);
    }

    // SEMANTICS

    public boolean conflictFree (ArgSet set) {
	if (!hasArgSet (set)) {
	    // set not in any extension
	    return false;
	}
	for (String a: set) {
	    for (String b: getDefeats(a)) {
		if (set.contains (b)) {
		    return false;
		}
	    }
	}
	return true;
    }

    public boolean admissibleGivenConflictFree (ArgSet set) {
	for (String a: set) {
	    if (!acceptable (set, a)) {
		return false;
	    }
	}
	return true;
    }

    public boolean admissible (ArgSet set) {
	return conflictFree (set) && admissibleGivenConflictFree (set);
    }

    public boolean stable (ArgSet set) {
	for (String a: args) {
	    if (!set.contains (a)) {
		boolean defeated = false;
		for (String b: set) {
		    if (getDefeats(b).contains (a)) {
			defeated = true;
			break;
		    }
		}
		if (!defeated) {
		    return false;
		}
	    }
	}
	return conflictFree (set);
    }

    public boolean completeGivenConflictFree (ArgSet set) {
	for (String a: args) {
	    if (!set.contains (a) && acceptable (set, a)) {
		return false;
	    } else if (set.contains (a) && !acceptable (set, a)) {
		return false;
	    }
	}
        return true;
    }

    public boolean completeGivenAdmissible (ArgSet set) {
	for (String a: args) {
	    if (!set.contains (a) && acceptable (set, a)) {
		return false;
	    }
	}
        return true;
    }

    public boolean complete (ArgSet set) {
	return conflictFree (set) && completeGivenConflictFree (set);
    }

    private boolean preferredHelper (ArgSet set, String curArg) {
	if (curArg != null && admissible (set)) {
	    // we added at least one argument and the set is admissible
	    return false;
	}
	int idx = curArg == null ? -1 : argsList.indexOf (curArg);
	for (int i=idx+1; i < argsList.size(); i++) {
	    String newArg = argsList.get (i);
	    if (set.contains (newArg)) {
		continue;
	    }
	    set.add (newArg);
	    if (!preferredHelper (set, newArg)) {
		return false;
	    }
	    set.remove (newArg);
	}
	return true;
    }

    public boolean preferred (ArgSet set) {
	return admissible(set) && preferredHelper (new ArgSet (set), null);
    }

    public boolean preferredGivenConflictFree (ArgSet set) {
	return admissibleGivenConflictFree(set) && preferredHelper (new ArgSet (set), null);
    }

    public boolean preferredGivenAdmissible (ArgSet set) {
	return preferredHelper (new ArgSet (set), null);
    }

    private boolean groundedHelper (ArgSet set, String curArg) {
	if (curArg != null && complete (set)) {
	    // we removed at least one argument and the set is complete
	    return false;
	}
	int idx = curArg == null ? -1 : argsList.indexOf (curArg);
	for (int i=idx+1; i < argsList.size(); i++) {
	    String newArg = argsList.get (i);
	    if (!set.contains (newArg)) {
		continue;
	    }
	    set.remove (newArg);
	    if (!groundedHelper (set, newArg)) {
		return false;
	    }
	    set.add (newArg);
	}
	return true;
    }

    public boolean grounded (ArgSet set) {
	return complete(set) && groundedHelper (new ArgSet (set), null);
    }

    public boolean groundedGivenConflictFree (ArgSet set) {
	return completeGivenConflictFree(set) && groundedHelper (new ArgSet (set), null);
    }

    public boolean groundedGivenAdmissible (ArgSet set) {
	return completeGivenAdmissible(set) && groundedHelper (new ArgSet (set), null);
    }

    public String toString () {
        StringBuilder b = new StringBuilder();
        for (String a: args) {
            b.append (a);
            b.append (" ");
        }
        b.append ("\n");
        for (String a: defeats.keySet()) {
	    for (String c: defeats.get(a)) {
		b.append ("{"+a+","+c+"}");
		b.append (" ");
	    }
        }
        return b.toString ();
    }
}

public class PAFTest {
    static Distribution nodeProb = new Distribution ();
    static Distribution numdefProb = new Distribution ();
    static Distribution defProb = new Distribution ();

    public static void main (String[] args) throws IOException {
        nodeProb.add (0.7, 0.1);
        nodeProb.add (0.8, 0.1);
        nodeProb.add (0.9, 0.7);
	nodeProb.add (1.0, 0.1);
        numdefProb.add (0, 0.1);
        numdefProb.add (1, 0.4);
        numdefProb.add (2, 0.5);
        defProb.add (0.6, 0.1);
        defProb.add (0.7, 0.1);
        defProb.add (0.8, 0.1);
        defProb.add (0.9, 0.7);
        
	//optTestArgsSameError ("Complete", "complete_same_error_01.csv", 1.96, 0.01, new CompleteSemantics(), new CompleteGivenConflictFreeSemantics());
	// optTestArgsSameError ("Complete", "complete_same_error_005.csv", 1.96, 0.005, new CompleteSemantics(), new CompleteGivenConflictFreeSemantics());
	optTestArgsSameError ("Grounded", "grounded_same_error_01.csv", 1.96, 0.01, new GroundedSemantics(), new GroundedGivenConflictFreeSemantics());
	//optTestArgsSameError ("Grounded", "grounded_same_error_005.csv", 1.96, 0.005, new GroundedSemantics(), new GroundedGivenConflictFreeSemantics());

	//testAdmissible ();
	//profOptimization ();
	//paperExamples ();
	//profExamples ();

        //testGenerator ();
        //testGraph ();
	//describeInstances ();
    }

    static void writeInstance (String graphfile, PAF paf, ArgSet set) {
        try {
            PrintWriter pw = new PrintWriter (new FileOutputStream (graphfile), true);
            pw.println (paf.toString ());
            pw.println (set.toString ());
            pw.close ();
	} catch (Exception e) {
	    e.printStackTrace ();
	}
    }

    static void writeDot (String dotfile, PAF paf, ArgSet set) {
	try {
            PrintWriter pw = new PrintWriter (new FileOutputStream (dotfile), true);
            pw.println ("digraph {");
            for (String a: paf.argsList) {
                if (set.contains (a)) {
                        pw.println ("\t"+a+" [shape=box];");
                }
                pw.println ("\t"+a+" [label=\""+a+"\\n"+paf.args.get(a)+"\"];");
                for (String b: paf.getDefeats(a).keySet()) {
                    pw.println ("\t"+a+" -> "+b+" [label="+paf.defeats.get(a).get(b)+"];");
                }
            }
            pw.println ("}");
            pw.close ();
        } catch (Exception e) {
            e.printStackTrace ();
        }
    }

    static class Instance {
        PAF paf;
        ArgSet set;

        public Instance (PAF paf, ArgSet set) {
            this.paf = paf;
            this.set = set;
        }
    }

    static Instance readInstance (String filename) {
        try {
            BufferedReader r = new BufferedReader (new FileReader (filename));
            PAF paf = new PAF();
            String[] args = r.readLine ().split (" ");
            for (String a: args) {
                if (!a.trim().equals ("")) {
                    String[] entry = a.trim().split(",");
                    paf.addArg (entry[0].trim(), Double.parseDouble(entry[1].trim()));
                }
            }
            String[] defs = r.readLine ().split (" ");
            for (String d: defs) {
                if (!d.trim().equals ("")) {
                    String[] entry = d.trim().split(",");
                    paf.addDefeat (entry[0].trim(), entry[1].trim(), Double.parseDouble (entry[2].trim()));
                }
            }
            ArgSet set = new ArgSet ();
            args = r.readLine().split (" ");
            for (String a: args) {
                if (a.trim() != "") {
                    set.add (a.trim());
                }
            }
            r.close ();
            return new Instance (paf, set);
        } catch (Exception e) {
            e.printStackTrace ();
        }
        return null;
    }

    static void describeInstances () throws IOException {
	PrintWriter pw = new PrintWriter (new FileOutputStream ("instances.csv"), true);
	pw.println ("Args,Defeats,Set size,CF,Admissible,Complete,Preferred,Grounded");
	for (int i=10; i <= 20; i++) {
	    System.out.println (i);
	    Instance pair = readInstance ("instances/instance"+i+".txt");
	    PAF paf = pair.paf;
	    ArgSet set = pair.set;
	    writeDot ("instances/instance"+i+".dot", paf, set);

	    Montecarlo m = new MontecarloError (1.96, 0.005);
	    double cf = paf.conflictFree(set);
	    double admissible = paf.admissible(set);
	    double complete = cf*m.run (paf, new CompleteGivenConflictFreeSemantics(), set).toDouble();
	    double preferred = cf*m.run (paf, new PreferredGivenConflictFreeSemantics(), set).toDouble();
	    double grounded = cf*m.run (paf, new GroundedGivenConflictFreeSemantics(), set).toDouble();
	    pw.println(i+","+paf.defeatsList.size()+","+set.size()+","+cf+","+admissible+","+complete+","+preferred+","+grounded);
	}
	pw.close ();
    }

    static void testGraph () {
        Instance pair = readInstance ("manual.txt");
        PAF paf = pair.paf;
        ArgSet set = pair.set;
        writeInstance ("manual.txt", paf, set);
        writeDot ("manual.txt", paf, set);
	System.out.println("Structures: "+paf.args.size()+" "+paf.defeatsList.size());
	System.out.println("Set size: "+set.size());
        double cf = paf.conflictFree(set);
        Montecarlo m = new MontecarloError (1.96, 0.005);
        System.out.println("Conflict free: "+cf);
        double p = m.run (paf, new CompleteGivenConflictFreeSemantics(), set).toDouble();
        System.out.println ("P(complete): "+(cf*p));
        p = m.run (paf, new PreferredGivenConflictFreeSemantics(), set).toDouble();
        System.out.println ("P(preferred): "+(cf*p));
        p = m.run (paf, new GroundedGivenConflictFreeSemantics(), set).toDouble();
        System.out.println ("P(grounded): "+(cf*p));
    }

    static void testGenerator () {
        PAF best = null;
        ArgSet sbest = null;
        double cfbest = 0;
        double compbest = 0;
        Montecarlo m = new MontecarloError (1.96, 0.0005);
        for (int i=0; i < 1000; i++) {
            Generator g = new Generator (20, nodeProb, numdefProb, defProb);
            PAF paf = g.generateTree ();
            System.out.println("Structures: "+paf.args.size()+" "+paf.defeatsList.size());
            System.out.println("Search space: "+(Math.pow(2, paf.args.size())*Math.pow(2, paf.defeatsList.size())));
            ArgSet set = paf.findPossibleSet (new GroundedGivenConflictFreeSemantics());
            System.out.println(set);
            double cf = paf.conflictFree(set);
            System.out.println("Conflict free: "+cf);
            if (cf > 0.6 && cf < 1) {
                double c = m.run (paf, new GroundedGivenConflictFreeSemantics(), set).toDouble();
                System.out.println ("P(semantic): "+c);
                if (c > compbest) {
                    best = paf;
                    sbest = set;
                    cfbest = cf;
                    compbest = c;
                    writeInstance ("graph.txt", paf, set);
                }
            }
        }
    }

    static Stats[] generateTreeAndRuns (int args, Montecarlo m, Semantics originalSemantics, Semantics optimizedSemantics) {
        System.out.println ("Args "+args);
        Generator g = new Generator (args, nodeProb, numdefProb, defProb);
        PAF paf = g.generateTree ();
        System.out.println("Nodes: "+paf.args.size()+" Defeats: "+paf.defeatsList.size());
        System.out.println("Search space: "+(Math.pow(2, paf.args.size())*Math.pow(2, paf.defeatsList.size())));
        ArgSet set = paf.findPossibleSet (optimizedSemantics);
        System.out.println(set);
        System.out.println("Conflict free: "+paf.conflictFree(set));
        
        Stats orig = m.runs (paf, originalSemantics, set, 20);
        Stats opt = m.runs (paf, optimizedSemantics, set, 20);
        return new Stats[]{orig, opt};
    }

    static Stats[] treeAndRuns (int args, Montecarlo m, Semantics exactSemantics, Semantics originalSemantics, Semantics optimizedSemantics) {
        Instance instance = readInstance ("instances/instance"+args+".txt");
        System.out.println ("Args "+args);
        PAF paf = instance.paf;
        System.out.println("Nodes: "+paf.args.size()+" Defeats: "+paf.defeatsList.size());
        System.out.println("Search space: "+(Math.pow(2, paf.args.size())*Math.pow(2, paf.defeatsList.size())));
        ArgSet set = instance.set;
        System.out.println(set);
        System.out.println("Conflict free: "+paf.conflictFree(set));

        Stats orig = m.runs (paf, originalSemantics, set, 20);
        Stats opt = m.runs (paf, optimizedSemantics, set, 20);
        if (exactSemantics != null) {
	    Montecarlo mex = new MontecarloError (1.96, 0.001);
            double exact = exactSemantics.conditional(paf, set)*mex.run (paf, exactSemantics, set).toDouble();
            orig.absError = Math.abs (orig.meanValue-exact);
            orig.relError = orig.absError / exact;
            opt.absError = Math.abs (opt.meanValue-exact);
            opt.relError = opt.absError / exact;
        }
        return new Stats[]{orig, opt};
    }

    static void optTestArgsSameTrials (String semanticName, String filename, int trials, Semantics originalSemantics, Semantics optimizedSemantics) throws IOException {
	PrintWriter pw = new PrintWriter (new FileOutputStream (filename), true);
	pw.println (semanticName+"; Trials="+trials+", Arguments, % CPU Time, Orig Time, Opt Time, Relative Error, Orig Error, Opt Error)");
        Montecarlo m = new MontecarloIter (trials);
	for (int args=10; args <= 20; args += 2) {
            Stats[] stats = treeAndRuns (args, new MontecarloIter (trials), null, originalSemantics, optimizedSemantics);
            Stats orig = stats[0];
            Stats opt = stats[1];
	    pw.println (args+","+(1.0)+","+(opt.meanTime/orig.meanTime)+","+orig.relError+","+opt.relError);
	}
	pw.close ();
    }

    static void optTestArgsSameError (String semanticName, String filename, double quantile, double error, Semantics originalSemantics, Semantics optimizedSemantics) throws IOException {
	PrintWriter pw = new PrintWriter (new FileOutputStream (filename), true);
	pw.println ("Args,"+Stats.headerString("Naive ")+","+Stats.headerString("Optim "));
        Montecarlo m = new MontecarloError (quantile, error);
	for (int args=10; args <= 20; args++) {
            Stats[] stats = treeAndRuns (args, m, null, originalSemantics, optimizedSemantics);
            Stats naive = stats[0];
            Stats optim = stats[1];
	    pw.println (args+","+naive.toString()+","+optim.toString());
	}
	pw.close ();
    }

    static void optTestArgsSameTime (String semanticName, String filename, long time, Semantics originalSemantics, Semantics optimizedSemantics) throws IOException {
	PrintWriter pw = new PrintWriter (new FileOutputStream (filename), true);
	pw.println (semanticName+"; time="+time+", Arguments, Relative Error, Orig Error, Opt Error");
        Montecarlo m = new MontecarloTimed (time);
	for (int args=10; args <= 20; args++) {
            Stats[] stats = treeAndRuns (args, m, new CompleteGivenConflictFreeSemantics(), originalSemantics, optimizedSemantics);
            Stats orig = stats[0];
            Stats opt = stats[1];
	    System.out.println ("Measured times: "+(orig.meanTime)+","+(opt.meanTime));
	    pw.println (args+","+orig.relError+","+opt.relError);
	}
	pw.close ();
    }

    static void testAdmissible () {
	PAF paf = new PAF();
	paf.addArgs ("a", 1.0,
		     "b", 2/3.0,
		     "c", 2/3.0,
		     "d", 1.0);
	paf.addDefeats ("a", "b", 2/3.0,
			"b", "c", 2/3.0);
	ArgSet s = new ArgSet ("a", "c", "d");
	Montecarlo m = new MontecarloError (1.96, 0.005);
	Semantics compl = new CompleteSemantics();
	Semantics complGA = new CompleteGivenAdmissibleSemantics();
	System.out.println("exact cf: "+paf.conflictFree (s));
	System.out.println("exact compl: "+paf.depthFirst (compl, s));
	System.out.println("exact adm: "+paf.depthFirst (new AdmissibleSemantics(), s));
	System.out.println("exact compl|A: "+paf.depthFirst (complGA, s));
	System.out.println("mc compl: "+m.run(paf, compl, s).toDouble());
	double p = m.run(paf, complGA, s).toDouble();
	System.out.println("mc compl|A: "+p);
	System.out.println("mc compl|A*A: "+complGA.conditional(paf, s)*p);
    }

    /*
    static void profOptimization () {
	PAF paf = new PAF();
	paf.addArgs ("a", 1.0,
		     "b", 2/3.0,
		     "c", 2/3.0,
		     "d", 1.0);
	paf.addDefeats ("a", "b", 2/3.0,
			"b", "c", 2/3.0);
	ArgSet s = new ArgSet ("a", "c", "d");
        //compareOptimization (paf, s);
    }

    public static void profExamples () {
	PAF paf = new PAF();
	paf.addArgs ("a", 1.0,
		     "b", 2/3.0,
		     "c", 2/3.0,
		     "d", 1.0);
	paf.addDefeats ("a", "b", 2/3.0,
			"b", "c", 2/3.0);
	ArgSet s = new ArgSet ("c");
	System.out.println (paf.montecarlo (new AdmissibleSemantics(), s, 1.96, 0.01));
	System.out.println (paf.depthFirst (new AdmissibleSemantics(), s)); // 0.37
        System.out.println (paf.admissible (s));
        System.out.println ();

	s = new ArgSet ("c", "d");
	System.out.println (paf.montecarlo (new AdmissibleSemantics(), s, 1.96, 0.01));
	System.out.println (paf.depthFirst (new AdmissibleSemantics(), s)); // 0.37
        System.out.println (paf.admissible (s));
        System.out.println ();

	s = new ArgSet ("a", "c", "d");
	System.out.println (paf.montecarlo (new AdmissibleSemantics(), s, 1.96, 0.01));
	System.out.println (paf.depthFirst (new AdmissibleSemantics(), s)); // 0.5679
        System.out.println (paf.admissible (s));
        System.out.println ();

	DAF daf = new DAF();
	daf.addArgs ("a", "b");
	daf.addDefeats ("a", "b",
			"b", "a");
	System.out.println (daf.complete (new ArgSet())+" "+daf.preferred (new ArgSet ()));
	System.out.println (daf.complete (new ArgSet("a"))+" "+daf.preferred (new ArgSet ("a")));
	System.out.println (daf.complete (new ArgSet("a", "b"))+" "+daf.preferred (new ArgSet ("a", "b")));
    }

    public static void paperExamples () {
	PAF paf = new PAF();
	paf.addArgs ("a", 1.0,
		     "b", 1.0,
		     "c", 0.7,
		     "d", 0.3);
	paf.addDefeats ("a", "c", 1.0,
			"d", "a", 1.0);
	ArgSet s = new ArgSet ("a", "b");
	System.out.println (paf.depthFirst (new CompleteSemantics(), s)); // 0.7
	System.out.println (paf.depthFirst (new GroundedSemantics(), s)); // 0.7
    }
    */
}

import java.util.*;
import java.io.*;

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

    // SEMANTICS

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
                for (String e: getDefeatedBy(d).keySet()) {
                    if (set.contains (e)) {
                        p32 *= 1-defeats.get(e).get(d);
                    }
                }
                p32 = args.get(d)*(1-p32);
                p3 *= p31+p32;
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

    public void removeArg (String name) {
	args.remove (name);
	argsList.remove (name);
	for (String b: getDefeatedBy (name)) {
	    defeats.get(b).remove (name);
	}
	for (String b: getDefeats (name)) {
	    defeatedBy.get(b).remove (name);
	}
	defeats.remove (name);
	defeatedBy.remove (name);
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

    public boolean stableGivenConflictFree (ArgSet set) {
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
	return true;
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

    public boolean stable (ArgSet set) {
	return conflictFree (set) && stableGivenConflictFree (set);
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

    public ArgSet initial () {
	ArgSet set = new ArgSet ();
	for (String a: argsList) {
	    if (getDefeatedBy(a).isEmpty ()) {
		set.add (a);
	    }
	}
	return set;
    }

    public DAF copy () {
	DAF daf = new DAF ();
	for (String a: argsList) {
	    daf.addArg (a);
	}
	for (String a: argsList) {
	    for (String b: getDefeats (a)) {
		daf.addDefeat (a, b);
	    }
	}
	return daf;
    }

    public ArgSet groundedSet () {
	DAF copy = copy ();
	ArgSet set = new ArgSet ();
	while (true) {
	    ArgSet newset = copy.initial ();
	    if (set.equals (newset)) {
		break;
	    }
	    set = newset;
	    ArgSet suppress = new ArgSet ();
	    for (String a: set) {
		for (String b: copy.getDefeats (a)) {
		    suppress.add (b);
		}
	    }
	    for (String a: suppress) {
		copy.removeArg (a);
	    }
	}
	return set;
    }

    public boolean grounded (ArgSet set) {
	return groundedSet().equals (set);
    }

    public boolean groundedGivenConflictFree (ArgSet set) {
	return grounded (set);
    }

    public boolean groundedGivenAdmissible (ArgSet set) {
	return grounded (set);
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

import java.util.*;

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

    public static Semantics fromName (String name) {
	if (name.equals ("null")) {
	    return null;
	}
	String[] split = name.split (" ");
	String className = split[0];
	int cacheSize = 0;
	if (split.length > 1) {
	    cacheSize = Integer.parseInt (split[1]);
	}
	try {
	    Semantics sem = (Semantics) Class.forName(className).newInstance ();
	    if (cacheSize > 0) {
		sem = new CachedSemantics (sem, cacheSize);
	    }
	    return sem;
	} catch (Exception e) {
	    throw new RuntimeException (e);
	}
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
	    // generate defeats that do not attack S
	    for (String a: daf.args) {
		for (String b: paf.getDefeats(a).keySet()) {
		    if (set.contains (b)) {
			// do it later
			continue;
		    }
		    if (daf.args.contains (b) && Math.random () <= paf.defeats.get(a).get(b)) {
			daf.addDefeat (a, b);
		    }
		}
	    }
	    // generate defeats that attack S
	    for (String a: set) {
		for (String b: paf.getDefeatedBy(a).keySet()) {
		    if (set.contains (b)) {
			// conflict
			continue;
		    }
		    if (daf.args.contains (b) && !set.contains (b)) {
			// "a" must be defended from "b" in the induced DAF
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
	    // generate defeats that attack S with one defender
	    for (String a: set) {
		for (String b: paf.getDefeatedBy(a).keySet()) {
		    if (set.contains (b)) {
			// conflict
			continue;
		    }
		    if (daf.args.contains (b)) {
			// generate one defender
			String defender = null;
			for (String c: paf.getDefeatedBy(b).keySet()) {
			    if (set.contains (c)) {
				defender = c;
				break;
			    }
			}
			if (defender != null && Math.random() <= paf.defeats.get(b).get(a)) {
			    daf.addDefeat (b, a);
			    if (!daf.getDefeats(defender).contains (b)) {
				daf.addDefeat (defender, b);
			    }
			}
		    }
		}
	    }
	    // generate defeats that do not attack S and that are not already in the DAF
	    for (String a: daf.args) {
		for (String b: paf.getDefeats(a).keySet()) {
		    if (set.contains (b)) {
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

class CompleteGivenAdmissibleSemantics extends GivenAdmissibleSemantics1 {
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

class StableGivenConflictFreeSemantics extends GivenConflictFreeSemantics {
    @Override
    public boolean evaluate (DAF daf, ArgSet set) {
	return daf.stableGivenConflictFree (set);
    }
}

class CachedSemantics extends Semantics {
    private int cacheSize;
    private ArgSet cacheSet; // cache only for this set of arguments
    private Semantics realSemantics;
    private LinkedHashMap<DAF, Boolean> cache = new LinkedHashMap<DAF, Boolean> () {
	protected boolean removeEldestEntry (Map.Entry eldest) {
	    return size() > cacheSize;
	}
    };

    public CachedSemantics (Semantics realSemantics, int cacheSize) {
	this.realSemantics = realSemantics;
	this.cacheSet = cacheSet;
	this.cacheSize = cacheSize;
    }

    public boolean evaluate (DAF daf, ArgSet set) {
	if (!set.equals (cacheSet)) {
	    cache.clear ();
	    cacheSet = set;
	}
	Boolean b = cache.get (daf);
	if (b != null) {
	    return b;
	}
	b = realSemantics.evaluate (daf, set);
	cache.put (daf, b);
	return b;
    }	

    public DAF montecarloSample (PAF paf, ArgSet set) {
	return realSemantics.montecarloSample (paf, set);
    }

    public boolean filterSample (DAF daf, ArgSet set) {
        return realSemantics.filterSample (daf, set);
    }

    public double conditional (PAF paf, ArgSet set) {
        return realSemantics.conditional (paf, set);
    }    
}

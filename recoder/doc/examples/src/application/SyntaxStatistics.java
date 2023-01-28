package application;
import java.lang.reflect.Modifier;
import java.util.Enumeration;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import recoder.CrossReferenceServiceConfiguration;
import recoder.convenience.AbstractTreeWalker;
import recoder.convenience.ForestWalker;
import recoder.java.SourceElement;
import recoder.util.Order;
import recoder.util.Sorting;

/**
   @author AL
 */
public class SyntaxStatistics {

    public static void main(String[] args) {
	CrossReferenceServiceConfiguration sc = 
	    new CrossReferenceServiceConfiguration();
	RecoderProgram.setup(sc, SyntaxStatistics.class, args);
	AbstractTreeWalker walker = 
	    new ForestWalker(sc.getSourceFileRepository().getCompilationUnits());
	while (walker.next()) {
	    add(walker.getProgramElement());
	}
	System.out.println("Occurances of COMPOST syntax node types:\n" + 
			   "(Supertypes are also included, abstract types are in parentheses)");
	System.out.print(format());
    }

    static Map<Class, Counter> counts = new HashMap<Class, Counter>();

    static class Counter extends Order.Identity {

	Object element;
	int count;
	
	Counter(Object t, int init) {
	    element = t;
	    count = init;
	}

	public int hashCode() {
	    return count;
	}
    }

    private static void add(SourceElement se) {
	Class t = se.getClass();
	Set<Class> supertypes = new HashSet();
	supertypes.add(t);
	collectSupertypes(t, supertypes);
	for (Class _t : supertypes) {
	    t = _t;
	    Counter c = counts.get(t);
	    if (c == null) {
		counts.put(t, new Counter(t, 1));
	    } else {
		c.count += 1;
	    }
	}
    }

    private static void collectSupertypes(Class t, Set types) {
	Class s = t.getSuperclass();
	if (s != null &&
	    SourceElement.class.isAssignableFrom(s) &&
	    !types.add(s)) {
	    collectSupertypes(s, types);
	}
	Class[] intf = t.getInterfaces();
	for (int i = 0; i < intf.length; i++) {
	    s = intf[i];
	    if (SourceElement.class.isAssignableFrom(s) &&
		!types.add(s)) {
		collectSupertypes(s, types);
	    }
	}	  
    }

    static String format() {
	Counter[] cnt = new Counter[counts.size()];
	int j = 0;
	for(Counter c : counts.values()) {
	    cnt[j++] = c;
	}
	Sorting.quickSort(cnt);
	StringBuffer result = new StringBuffer();
	for (int i = 0; i < cnt.length; i++) {
	    Counter c = cnt[i];
	    if (c == null) {
		result.append('0');
	    } else {
		result.append(c.count);
	    }
	    result.append(' ');
	    Class cl = (Class)c.element;
	    if (Modifier.isAbstract(cl.getModifiers())) {
		result.append('(');
	    }
	    result.append(cl.getName());
	    if (Modifier.isAbstract(cl.getModifiers())) {
		result.append(')');
	    }
	    result.append('\n');
	}
	return result.toString();
    }
}

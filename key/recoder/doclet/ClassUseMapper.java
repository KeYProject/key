/*
 * @(#)ClassUseMapper.java	1.4 00/02/02
 *
 * Copyright 1998-2000 Sun Microsystems, Inc. All Rights Reserved.
 * 
 * This software is the proprietary information of Sun Microsystems, Inc.  
 * Use is subject to license terms.
 * 
 */



import com.sun.javadoc.*;
import com.sun.tools.doclets.ClassTree;
import com.sun.tools.doclets.DocletAbortException;
import java.util.*;

/**
 * @since JDK1.2
 * @author Robert G. Field
 */
public class ClassUseMapper {

    private final ClassTree classtree;

    /**
     * Mapping of ClassDocs to set of PackageDoc used by that class.
     * Entries may be null.
     */
    public Map classToPackage = new HashMap();

    /**
     * Mapping of ClassDocs to set of ClassDoc used by that class.
     * Entries may be null.
     */
    public Map classToClass = new HashMap();

    /**
     * Mapping of ClassDocs to list of ClassDoc which are direct or 
     * indirect subclasses of that class.
     * Entries may be null.
     */
    public Map classToSubclass = new HashMap();

    /**
     * Mapping of ClassDocs to list of ClassDoc which are direct or 
     * indirect subinterfaces of that interface.
     * Entries may be null.
     */
    public Map classToSubinterface = new HashMap();

    /**
     * Mapping of ClassDocs to list of ClassDoc which implement
     * this interface.
     * Entries may be null.
     */
    public Map classToImplementingClass = new HashMap();

    /**
     * Mapping of ClassDocs to list of FieldDoc declared as that class.
     * Entries may be null.
     */
    public Map classToField = new HashMap();

    /**
     * Mapping of ClassDocs to list of MethodDoc returning that class.
     * Entries may be null.
     */
    public Map classToMethodReturn = new HashMap();

    /**
     * Mapping of ClassDocs to list of MethodDoc having that class
     * as an arg.
     * Entries may be null.
     */
    public Map classToMethodArgs = new HashMap();

    /**
     * Mapping of ClassDocs to list of MethodDoc which throws that class.
     * Entries may be null.
     */
    public Map classToMethodThrows = new HashMap();

    /**
     * Mapping of ClassDocs to list of ConstructorDoc having that class
     * as an arg.
     * Entries may be null.
     */
    public Map classToConstructorArgs = new HashMap();

    /**
     * Mapping of ClassDocs to list of ConstructorDoc which throws that class.
     * Entries may be null.
     */
    public Map classToConstructorThrows = new HashMap();


    /**
     * Write out class use pages.
     */
    public static void generate(RootDoc root, 
                       ClassTree classtree) throws DocletAbortException {
        ClassUseMapper mapper = new ClassUseMapper(root, classtree);
        ClassDoc[] classes = root.classes();
        for (int i = 0; i < classes.length; i++) {
            ClassUseWriter.generate(mapper, classes[i]);
        }
        PackageDoc[] pkgs = Standard.configuration().packages;
        for (int i = 0; i < pkgs.length; i++) {
            PackageUseWriter.generate(mapper, pkgs[i]);
        }
    }

    private ClassUseMapper(RootDoc root, ClassTree classtree) {
        this.classtree = classtree;

        // Map subclassing, subinterfacing implementing, ...
        for (Iterator it = classtree.baseclasses().iterator(); it.hasNext();) {
	    subclasses((ClassDoc)it.next());
	}
        for (Iterator it = classtree.baseinterfaces().iterator(); it.hasNext();) {
	    // does subinterfacing as side-effect
	    implementingClasses((ClassDoc)it.next());
	}
	// Map methods, fields, constructors using a class.
        ClassDoc[] classes = root.classes();
        for (int i = 0; i < classes.length; i++) {
            ClassDoc cd = classes[i];
            FieldDoc[] fields = cd.fields();
            for (int j = 0; j < fields.length; j++) {
                FieldDoc fd = fields[j];
                ClassDoc tcd = fd.type().asClassDoc();
                if (tcd != null) {
                    add(classToField, tcd, fd);
                }
            }
            ConstructorDoc[] cons = cd.constructors();
            for (int j = 0; j < cons.length; j++) {
                mapExecutable(cons[j]);
            }
            MethodDoc[] meths = cd.methods();
            for (int j = 0; j < meths.length; j++) {
                MethodDoc md = meths[j];
                mapExecutable(md);
                ClassDoc tcd = md.returnType().asClassDoc();
                if (tcd != null) {
                    add(classToMethodReturn, tcd, md);
                }
            }
        }
    }

    /**
     * Return all subclasses of a class AND fill-in classToSubclass map.
     */
    private Collection subclasses(ClassDoc cd) {
        Collection ret = (Collection)classToSubclass.get(cd);
	if (ret == null) {
	    ret = new TreeSet();
	    List subs = classtree.subclasses(cd);
	    if (subs != null) {
	        ret.addAll(subs);
		for (Iterator it = subs.iterator(); it.hasNext();) {
		    ret.addAll(subclasses((ClassDoc)it.next()));
		}
	    }
	    addAll(classToSubclass, cd, ret);
	}
	return ret;
    }
	    
    /**
     * Return all subinterfaces of an interface AND fill-in classToSubinterface map.
     */
    private Collection subinterfaces(ClassDoc cd) {
        Collection ret = (Collection)classToSubinterface.get(cd);
	if (ret == null) {
	    ret = new TreeSet();
	    List subs = classtree.subinterfaces(cd);
	    if (subs != null) {
	        ret.addAll(subs);
		for (Iterator it = subs.iterator(); it.hasNext();) {
		    ret.addAll(subinterfaces((ClassDoc)it.next()));
		}
	    }
	    addAll(classToSubinterface, cd, ret);
	}
	return ret;
    }
	    
    /**
     * Return all implementing classes of an interface (including
     * all subclasses of implementing classes and all classes 
     * implementing subinterfaces) AND fill-in both classToImplementingClass 
     * and classToSubinterface maps.
     */
    private Collection implementingClasses(ClassDoc cd) {
        Collection ret = (List)classToImplementingClass.get(cd);
	if (ret == null) {
	    ret = new TreeSet();
	    List impl = classtree.implementingclasses(cd);
	    if (impl != null) {
	        ret.addAll(impl);
	        for (Iterator it = impl.iterator(); it.hasNext();) {
		    ret.addAll(subclasses((ClassDoc)it.next()));
		}
	    }
	    for (Iterator it = subinterfaces(cd).iterator(); it.hasNext();) {
	        ret.addAll(implementingClasses((ClassDoc)it.next()));
	    }
	    addAll(classToImplementingClass, cd, ret);
	}
	return ret;
    }
	    
    /**
     * Determine classes used by a method or constructor, so they can be
     * inverse mapped.
     */
    private void mapExecutable(ExecutableMemberDoc em) {
        Parameter[] params = em.parameters();
        boolean isConstructor = em.isConstructor();
        List classArgs = new ArrayList();
        for (int k = 0; k < params.length; k++) {
            ClassDoc pcd = params[k].type().asClassDoc();
            // primitives don't get mapped, also avoid dups
            if (pcd != null && !classArgs.contains(pcd)) {
                add(isConstructor? classToConstructorArgs :classToMethodArgs,
                    pcd, em);
                classArgs.add(pcd);
            }
        }
        ClassDoc[] thr = em.thrownExceptions();
        for (int k = 0; k < thr.length; k++) {
            add(isConstructor? classToConstructorThrows : classToMethodThrows, 
                thr[k], em);
        }        
    }

    private List refList(Map map, ClassDoc cd) {
        List list = (List)map.get(cd);
        if (list == null) {
            list = new ArrayList();
            map.put(cd, list);
        }
        return list;
    }

    private Set packageSet(ClassDoc cd) {
	Set pkgSet = (Set)classToPackage.get(cd);
        if (pkgSet == null) {
            pkgSet = new TreeSet();
            classToPackage.put(cd, pkgSet);
        }
        return pkgSet;
    }

    private Set classSet(ClassDoc cd) {
	Set clsSet = (Set)classToClass.get(cd);
        if (clsSet == null) {
            clsSet = new TreeSet();
            classToClass.put(cd, clsSet);
        }
        return clsSet;
    }

    private void add(Map map, ClassDoc cd, ProgramElementDoc ref) {
 	// add to specified map
        refList(map, cd).add(ref);

	// add ref's package to package map and class map
	packageSet(cd).add(ref.containingPackage());
        classSet(cd).add(ref instanceof MemberDoc? 
                         ((MemberDoc)ref).containingClass() :
                         ref);
    }

    private void addAll(Map map, ClassDoc cd, Collection refs) {
        if (refs == null) {
	    return;
	}
	// add to specified map
        refList(map, cd).addAll(refs);

	Set pkgSet = packageSet(cd);
	Set clsSet = classSet(cd);
	// add ref's package to package map and class map
	for (Iterator it = refs.iterator(); it.hasNext();) {
            ProgramElementDoc pedoc = (ProgramElementDoc)it.next();
	    pkgSet.add(pedoc.containingPackage());
            clsSet.add(pedoc instanceof MemberDoc? 
                       ((MemberDoc)pedoc).containingClass() :
                       pedoc);
	}
    }
}

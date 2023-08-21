/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.service;

import java.util.*;

import recoder.ServiceConfiguration;
import recoder.TuningParameters;
import recoder.abstraction.*;
import recoder.abstraction.Package;
import recoder.convenience.Format;
import recoder.convenience.TreeWalker;
import recoder.io.SourceFileRepository;
import recoder.java.*;
import recoder.java.declaration.AnnotationElementValuePair;
import recoder.java.declaration.InheritanceSpecification;
import recoder.java.declaration.TypeArgumentDeclaration;
import recoder.java.declaration.VariableDeclaration;
import recoder.java.expression.operator.New;
import recoder.java.reference.*;
import recoder.util.Debug;
import recoder.util.ProgressEvent;

/**
 * Implements queries for cross referencing.
 *
 * @author AL
 */
public class DefaultCrossReferenceSourceInfo extends DefaultSourceInfo
        implements CrossReferenceSourceInfo {

    /**
     * Cache mapping elements to known references.
     */
    // private final MutableMap/* <ProgramModelElement, Set <Reference>> */
    // element2references = new IdentityHashTable(256);
    private final Map<ProgramModelElement, Set<Reference>> element2references =
        new HashMap<>(256);

    /**
     * Creates a new service.
     *
     * @param config the configuration this services becomes part of.
     */
    public DefaultCrossReferenceSourceInfo(ServiceConfiguration config) {
        super(config);
    }

    /**
     * Change notification callback method.
     *
     * @param config the configuration this services becomes part of.
     */
    public void modelChanged(ChangeHistoryEvent changes) {

        // Java allows use before definition, so as the first pass we
        // have to update scopes; this is done by the SourceInfo.

        // super.modelChanged(changes);

        List<TreeChange> changed = changes.getChanges();
        int s = changed.size();

        int c = 0;
        listeners.fireProgressEvent(0, 3 * s, "Building Scopes");

        // detached first
        for (TreeChange tc : changed) {
            if (tc instanceof DetachChange) {
                if (!tc.isMinor()) {
                    processChange(tc);
                }
                listeners.fireProgressEvent(++c);
            }
        }
        for (TreeChange tc : changed) {
            if (tc instanceof AttachChange) {
                if (!tc.isMinor()) {
                    processChange(tc);
                }
                listeners.fireProgressEvent(++c);
            }
        }

        listeners.fireProgressEvent(c, "Resolving References");

        TreeWalker tw = new TreeWalker(null);
        // TreeChangeList changed = changes.getChanges();
        // int s = changed.size();
        for (TreeChange tc : changed) {
            if (tc instanceof DetachChange) {
                if (!tc.isMinor()) {
                    ProgramElement pe = tc.getChangeRoot();
                    boolean rippleEffect = isPossiblyShowingRippleEffect(tc);
                    if (pe instanceof TypeArgumentDeclaration) {
                        // this may invalidate the parent reference...
                        reset(true);
                        return;
                    } else if (pe instanceof Reference) {
                        // TODO we can most probably handle AnnotationUse more efficiently
                        if (!rippleEffect) {
                            // nothing bad may happen in this context
                            deregisterReference((Reference) pe);
                        } else {
                            // We would have to remove this reference from
                            // the entity it belongs to and do this
                            // transitively for the outer reference.
                            // If this is a type reference in
                            // an inheritance specification, we have a problem.
                            reset(true);
                            return;
                        }
                    } else if (pe instanceof ProgramModelElement
                            || pe instanceof VariableDeclaration) {
                        // We would have to revalidate all references to
                        // this element.
                        // TODO deleting a single constructor which takes no parameters can be
                        // improved! (regardless of visibility)
                        reset(true);
                        return;
                    } else if (pe instanceof InheritanceSpecification) {
                        // References to supertype members may have changed
                        reset(true);
                        return;
                    } else if (pe instanceof AnnotationElementValuePair) {
                        // may invalidate the reference of an annotation use
                        reset(true);
                        return;
                    }
                    tw.reset(pe);
                    tw.next(); // skip pe
                    while (tw.next()) {
                        ProgramElement p = tw.getProgramElement();
                        if (p instanceof Reference) {
                            deregisterReference((Reference) p);
                        }
                    }
                }
                listeners.fireProgressEvent(++c);
            }
        }
        for (TreeChange tc : changed) {
            if (tc instanceof AttachChange) {
                if (!tc.isMinor()) {
                    ProgramElement pe = tc.getChangeRoot();
                    NonTerminalProgramElement pa = tc.getChangeRootParent();
                    if (pe instanceof TypeArgumentDeclaration) {
                        // this may invalidate the parent reference...
                        reset(true);
                        return;
                    } else if (pe instanceof Reference) {
                        // TODO we can most probably handle AnnotationUse more efficiently
                        if (pe instanceof Expression &&
                        // var ref, field ref, method ref, constr ref
                                !isPossiblyShowingRippleEffect(tc)) {
                            // nothing bad may happen
                        } else {
                            // We would have to handle type references in
                            // inheritance specifications. Hard work.
                            reset(true);
                            return;
                        }
                    } else if (pe instanceof ProgramModelElement
                            || pe instanceof VariableDeclaration) {
                        // We would have to find out whether this element
                        // hides some other element that is already referred to.
                        // If so, we must revalidate those elements.
                        // Further, overloading must be considered.
                        // Program model elements in subtrees are not relevant
                        // as they must be in an inner scope (really?) and
                        // cannot have been referred to.
                        // TODO replacing a default constructor can be improved, if proper
                        // visibility
                        reset(true);
                        return;
                    } else if (pe instanceof InheritanceSpecification) {
                        // References to supertype members may have changed
                        reset(true);
                        return;
                    } else if (pe instanceof AnnotationElementValuePair) {
                        // may invalidate the reference of an annotation use
                        reset(true);
                        return;
                    }
                }
                listeners.fireProgressEvent(++c);
            }
        }
        for (TreeChange tc : changed) {
            if (!tc.isMinor() && (tc instanceof AttachChange)) {
                AttachChange ac = (AttachChange) tc;
                ProgramElement pe = ac.getChangeRoot();
                // we expect that scopes are valid
                analyzeReferences(pe);
            }
            listeners.fireProgressEvent(++c);
        }
    }

    private boolean isPossiblyShowingRippleEffect(TreeChange tc) {
        // triggers a bug
        /*
         * NonTerminalProgramElement q = tc.getChangeRootParent(); // enclosed in statement and no
         * ref or decl in the way do { if (q instanceof Reference || q instanceof Declaration) {
         * return true; } if (q instanceof Statement) { // no Reference! return false; } q =
         * q.getASTParent(); } while (q != null);
         */
        return true;
    }

    /**
     * Retrieves the list of references to a given method (or constructor). The references stem from
     * all known compilation units.
     *
     * @param m a method.
     * @return a possibly empty list of references to the given method.
     */
    public List<MemberReference> getReferences(Method m) {
        Debug.assertNonnull(m);
        updateModel();
        Set references = element2references.get(m);
        if (references == null) {
            return new ArrayList<>(0);
        }
        int s = references.size();
        if (s == 0) {
            return new ArrayList<>(0);
        }
        List<MemberReference> result = new ArrayList<>(s);
        for (Object o : references) {
            result.add((MemberReference) o);
        }
        return result;
    }

    /**
     * Retrieves the list of references to a given constructor. The references stem from all known
     * compilation units.
     *
     * @param c a constructor.
     * @return a possibly empty list of references to the given constructor.
     */
    public List<ConstructorReference> getReferences(Constructor c) {
        Debug.assertNonnull(c);
        updateModel();
        Set<Reference> references = element2references.get(c);
        if (references == null) {
            return new ArrayList<>(0);
        }
        int s = references.size();
        if (s == 0) {
            return new ArrayList<>(0);
        }
        List<ConstructorReference> result = new ArrayList<>(s);
        for (Reference o : references) {
            result.add((ConstructorReference) o);
        }
        return result;
    }

    /**
     * Retrieves the list of references to a given variable. The references stem from all known
     * compilation units.
     *
     * @param v a variable.
     * @return a possibly empty list of references to the given variable.
     */
    public List<VariableReference> getReferences(Variable v) {
        Debug.assertNonnull(v);
        updateModel();
        Set references = element2references.get(v);
        if (references == null) {
            return new ArrayList<>(0);
        }
        int s = references.size();
        if (s == 0) {
            return new ArrayList<>(0);
        }
        List<VariableReference> result = new ArrayList<>(s);
        for (Object o : references) {
            result.add((VariableReference) o);
        }
        return result;
    }

    /**
     * Retrieves the list of references to a given field. The references stem from all known
     * compilation units.
     *
     * @param f a field.
     * @return a possibly empty list of references to the given field.
     */
    public List<FieldReference> getReferences(Field f) {
        Debug.assertNonnull(f);
        updateModel();
        Set references = element2references.get(f);
        if (references == null) {
            return new ArrayList<>(0);
        }
        int s = references.size();
        if (s == 0) {
            return new ArrayList<>(0);
        }
        List<FieldReference> result = new ArrayList<>(s);
        for (Object o : references) {
            result.add((FieldReference) o);
        }
        return result;
    }

    /**
     * Retrieves the list of references to a given type. The references stem from all known
     * compilation units.
     *
     * @param t a type.
     * @return a possibly empty list of references to the given type.
     */
    public List<TypeReference> getReferences(Type t) {
        Debug.assertNonnull(t);
        updateModel();
        Set<Reference> references = element2references.get(t);
        if (references == null) {
            return new ArrayList<>(0);
        }
        int s = references.size();
        if (s == 0) {
            return new ArrayList<>(0);
        }
        List<TypeReference> result = new ArrayList<>(s);
        for (Reference r : references) {
            result.add((TypeReference) r);
        }
        return result;
    }

    /**
     * Retrieves the list of references to a given package. The references stem from all known
     * compilation units.
     *
     * @param p a package.
     * @return a possibly empty list of references to the given package.
     */
    public List<PackageReference> getReferences(Package p) {
        Debug.assertNonnull(p);
        updateModel();
        Set<Reference> references = element2references.get(p);
        if (references == null) {
            return new ArrayList<>(0);
        }
        int s = references.size();
        if (s == 0) {
            return new ArrayList<>(0);
        }
        List<PackageReference> result = new ArrayList<>(s);
        for (Reference pr : references) {
            result.add((PackageReference) pr);
        }
        return result;
    }

    private void registerReference(Reference ref, ProgramModelElement pme) {
        Set<Reference> set = element2references.computeIfAbsent(pme, k -> new HashSet<>(
            TuningParameters.INITIAL_CROSS_REFERENCER_ELEMENT2REFERENCE_HASH_SET_SIZE));
        set.add(ref);
    }

    private void deregisterReference(Reference ref) {
        ProgramModelElement pme = reference2element.get(ref);
        if (pme == null) {
            // ThisReference
            return;
        }
        Set set = element2references.get(pme);
        if (set == null) {
            // ThisReference
        } else {
            set.remove(ref);
        }
    }

    /**
     * Collects all Method-, Constructor-, Variable- and TypeReferences in the subtree.
     */
    private void analyzeReferences(ProgramElement pe) {
        if (pe instanceof NonTerminalProgramElement) {
            NonTerminalProgramElement nt = (NonTerminalProgramElement) pe;
            for (int i = 0, c = nt.getChildCount(); i < c; i += 1) {
                analyzeReferences(nt.getChildAt(i));
            }
        } else {
            return;
        }
        if (pe instanceof Reference) {
            if (pe instanceof UncollatedReferenceQualifier) {
                try {
                    pe = resolveURQ((UncollatedReferenceQualifier) pe);
                } catch (ClassCastException cce) {
                    getErrorHandler().reportError(new UnresolvedReferenceException(
                        Format.toString("Could not resolve " + ELEMENT_LONG, pe), pe));
                    // this might have been a field or class or package
                    // we have to let this URQ remain alive
                }
            }
            // no else
            if (pe instanceof VariableReference) {
                VariableReference vr = (VariableReference) pe;
                Variable v = getVariable(vr);
                if (v == null) {
                    getErrorHandler().reportError(new UnresolvedReferenceException(
                        Format.toString("Could not resolve " + ELEMENT_LONG, vr), vr));
                    v = getNameInfo().getUnknownField();
                }
                registerReference(vr, v);
            } else if (pe instanceof TypeReference) {
                TypeReference tr = (TypeReference) pe;
                Type t = getType(tr);
                if (t instanceof ParameterizedType) {
                    t = ((ParameterizedType) t).getGenericType();
                }
                if (t != null) { // void type otherwise
                    if (!(t instanceof DefaultNameInfo.UnknownClassType)) {
                        registerReference(tr, t);
                        if (t instanceof ClassType) {
                            ClassType subType = null;
                            TypeReferenceContainer parent = tr.getParent();
                            if (parent instanceof InheritanceSpecification) {
                                subType = ((InheritanceSpecification) parent).getParent();
                            } else if (parent instanceof New) {
                                subType = ((New) parent).getClassDeclaration();
                            }
                            if (subType != null) {
                                ClassType superType = (ClassType) t;
                                ProgramModelInfo pmi = superType.getProgramModelInfo();
                                ((DefaultProgramModelInfo) pmi).registerSubtype(subType, superType);
                            }
                        }
                    }
                }
            } else if (pe instanceof MethodReference) {
                MethodReference mr = (MethodReference) pe;
                Method m = getMethod(mr);
                registerReference(mr, m);
            } else if (pe instanceof ConstructorReference) {
                ConstructorReference cr = (ConstructorReference) pe;
                Constructor c = getConstructor(cr);
                registerReference(cr, c);
            } else if (pe instanceof AnnotationPropertyReference) {
                AnnotationPropertyReference apr = (AnnotationPropertyReference) pe;
                AnnotationProperty ap = getAnnotationProperty(apr);
                registerReference(apr, ap);
            } else if (pe instanceof PackageReference) {
                PackageReference pr = (PackageReference) pe;
                Package p = getPackage(pr);
                registerReference(pr, p);
            }
        }
    }

    /*
     * public TypeDeclarationList getSubtypes(ClassType ct) { Debug.assert(ct); updateModel();
     * TypeReferenceList refs = getReferences(ct); if (refs == null) { return
     * TypeDeclarationList.EMPTY_LIST; } TypeDeclarationMutableList result = new
     * TypeDeclarationArrayList(); for (int i = refs.size() - 1; i >= 0; i -= 1) { TypeReference tr
     * = refs.getTypeReference(i); ProgramElement parent = tr.getASTParent(); if (parent instanceof
     * InheritanceSpecification) { InheritanceSpecification is = (InheritanceSpecification)parent;
     * result.add(is.getParent()); } } return result; }
     *
     * public TypeDeclarationList getAllSubtypes(ClassType ct) { ClassTypeTopSort ctts = new
     * SubTypeTopSort(); List<ClassType> ctl = ctts.getAllTypes(ct); int s = ctl.size();
     * TypeDeclarationMutableList result = new TypeDeclarationArrayList(s - 1); // begin at second
     * entry - the top sort includes the input class for (int i = 1; i < s; i += 1) { ClassType t =
     * ctl.getClassType(i); if (t instanceof TypeDeclaration) { result.add((TypeDeclaration)t); } }
     * return result; }
     */

    public String information() {
        updateModel();
        int c1 = 0, c2 = 0, c3 = 0, c4 = 0, c5 = 0;
        int r1 = 0, r2 = 0, r3 = 0, r4 = 0, r5 = 0;
        for (ProgramModelElement pme : element2references.keySet()) {
            Set set = element2references.get(pme);
            int size = set == null ? 0 : set.size();
            if (pme instanceof Variable) {
                c1 += 1;
                r1 += size;
            } else if (pme instanceof Method) {
                if (pme instanceof Constructor) {
                    c3 += 1;
                    r3 += size;
                } else {
                    c2 += 1;
                    r2 += size;
                }
            } else if (pme instanceof Type) {
                // System.err.println(Format.toString("%N %i", pme));
                c4 += 1;
                r4 += size;
            } else if (pme instanceof Package) {
                c5 += 1;
                r5 += size;
            }
        }
        return "" + c1 + " variables with " + r1 + " references\n" + c2 + " methods with " + r2
            + " references\n" + c3 + " constructors with " + r3 + " references\n" + c4
            + " types with " + r4 + " references\n" + c5 + " packages with " + r5 + " references";
    }

    /*
     * private void dumpTable(MutableMap table, PrintStream out) { int size = table.size();
     * ProgramModelElement[] refs = new ProgramModelElement[size]; java.util.Enumeration e =
     * table.keys(); for (int i = 0; i < size; i++) { refs[i] =
     * (ProgramModelElement)e.nextElement(); } Sorting.heapSort(refs,
     * NamedModelElement.LEXICAL_ORDER); for (int j = 0; j < size; j++) { ProgramModelElement x =
     * refs[j]; ProgramElementList list = (ProgramElementList)table.get(x);
     * out.print(Format.toString("%N <- ", x)); for (int i = 0, s = (list == null) ? 0 :
     * list.size(); i < s; i++) { out.print(Format.toString("%p ", list.getProgramElement(i))); }
     * out.println(); } }
     */

    /*
     * public long checksum() { int size = element2references.size(); ProgramModelElement[] elem =
     * new ProgramModelElement[size]; Enumeration enum = element2references.keys(); for (int i =
     * size - 1; i >= 0; i -= 1) { elem[i] = (ProgramModelElement)enum.nextElement(); }
     * Sorting.heapSort(elem, ProgramModelElement.LEXICAL_ORDER); java.util.zip.CRC32 chksum = new
     * java.util.zip.CRC32(); for (int j = size - 1; j >= 0; j -= 1) { ProgramModelElement pme =
     * elem[j]; StringBuffer buf = new StringBuffer(Format.toString("%N:", pme)); Map list =
     * (Map)element2references.get(pme); if (list != null) { int lsize = list.size(); String[] str =
     * new String[lsize]; for (int i = lsize - 1; i >= 0; i -= 1) { str[i] =
     * Format.toString("%p(%u) ", (ProgramElement)list.getObject(i)); } Sorting.heapSort(str,
     * Order.LEXICAL); for (int i = 0; i < lsize; i += 1) { buf.append(str[i]); } }
     * chksum.update(buf.toString().getBytes()); } return chksum.getValue(); }
     */

    private void reset(boolean fire) {
        super.reset();
        element2references.clear();
        SourceFileRepository sfr = serviceConfiguration.getSourceFileRepository();
        List<CompilationUnit> cul = sfr.getCompilationUnits();
        int c = 0;
        if (fire) {
            ProgressEvent pe = listeners.getLastProgressEvent();
            c = pe.getWorkDoneCount();
            listeners.fireProgressEvent(c, c + cul.size());
        }
        for (int i = cul.size() - 1; i >= 0; i -= 1) {
            CompilationUnit cu = cul.get(i);
            analyzeReferences(cu);
            if (fire) {
                listeners.fireProgressEvent(++c);
            }
        }
    }

    /**
     * Resets all observable parts of the model.
     */
    public void reset() {
        reset(false);
    }

    class SubTypeTopSort extends ClassTypeTopSort {

        protected final List<ClassType> getAdjacent(ClassType c) {
            return getSubtypes(c);
        }
    }
}

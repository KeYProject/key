package de.uka.ilkd.key.visualdebugger;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
//import visualdebugger.astops.*;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.IteratorOfType;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.ListOfType;
import de.uka.ilkd.key.java.abstraction.SLListOfType;
import de.uka.ilkd.key.java.declaration.MethodDeclaration;
import de.uka.ilkd.key.logic.ListOfTerm;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.SLListOfTerm;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.ProblemLoader;

/**
 * The Class WatchPointManager keeps a list of all watchpoints.
 */
public class WatchPointManager {

    /** The watch points. */
    private LinkedList<WatchPoint> watchPoints = new LinkedList<WatchPoint>();

    private ListOfTerm listOfWatchpoints;

    /**
     * Gets the watch points.
     * 
     * @return the watch points
     */
    public LinkedList<WatchPoint> getWatchPoints() {
        return watchPoints;
    }

    /**
     * Gets the watch points as array.
     * 
     * @return the watch points as array
     */
    public Object[] getWatchPointsAsArray() {
        return watchPoints.toArray();
    }

    /**
     * Adds the watch point.
     * 
     * @param wp
     *                the wp
     */
    public void addWatchPoint(WatchPoint wp) {
        watchPoints.add(wp);
    }

    /**
     * Removes the watch point.
     * 
     * @param wp
     *                the wp
     */
    public void removeWatchPoint(WatchPoint wp) {

        if (watchPoints.contains(wp)) {
            watchPoints.remove(wp);
        }
    }

    /**
     * Translates the WatchPoints into KeY data structures.
     * 
     * @return the number of translated WatchPoints
     */
    private int translateWatchpoints(Services services) {

        LinkedList<WatchPoint> watchpoints = getWatchPoints();
        listOfWatchpoints = SLListOfTerm.EMPTY_LIST;
        try {
            assert (watchpoints != null): "Watchpoints are NULL!";

            if (watchpoints.isEmpty()) {
                return 0;
            } else {

                Namespace progVarNS = new Namespace();

                final JavaInfo ji = services.getJavaInfo();

                for (int i = 0; i < watchpoints.size(); i++) {

                    WatchPoint wp = watchpoints.get(i);

                    if (wp.isEnabled()) {
                        StringBuffer buffer = new StringBuffer();
                        String declaringType = wp.getDeclaringType();

                        String nameOfSelf = "self_XY";
                        ProgramElementName selfName = new ProgramElementName(
                                nameOfSelf);

                        // check namespace
                        while (services.getNamespaces().lookup(selfName) != null) {
                            nameOfSelf = nameOfSelf.concat("Z");
                            selfName = new ProgramElementName(nameOfSelf);
                        }

                        ProgramVariable var_self = new LocationVariable(
                                selfName, ji.getKeYJavaType(declaringType));
                        ProgramVariable var_dummy = new LocationVariable(
                                new ProgramElementName(wp.getName()), services
                                        .getTypeConverter().getBooleanType());
                        progVarNS.add(var_self);
                        progVarNS.add(var_dummy);

                        if (wp.getLocalVariables() != null &&  wp.getLocalVariables().size() > 0) {
                            // TODO Locals
                            List<LocalVariableDescriptor> locVars = wp.getLocalVariables();
                            //***
                            List<String> parameterTypes = wp.getParameterTypes();
                            ListOfType signature = SLListOfType.EMPTY_LIST;
                            for (String string : parameterTypes) {
                                signature = signature.append(ji.getKeYJavaType(string));
                            }

                            KeYJavaType classType = ji.getKeYJavaType(wp.getDeclaringType());
                            ProgramMethod pm  = ji.getProgramMethod(classType, wp.getMethod(), signature, classType);
                            System.out.println("programmethod "+pm.getFullName());
                            MethodDeclaration md = pm.getMethodDeclaration();
                            
                            HashSet<ProgramElement> pvs = new HashSet<ProgramElement>();
                            MethodVisitor pvc = new MethodVisitor(pm, locVars);
                            pvc.start();
                            pvs.addAll(pvc.result());
                            for (ProgramElement programElement : pvs) {
                                System.out.println("result of visting method: " + programElement.getClass() + " "+ programElement.toString());
                            }
                            //***
                            
                            for (LocalVariableDescriptor localVariableDescriptor : locVars) {
                            
                                System.out.println("type: " +localVariableDescriptor.getType());
                                System.out.println("name: " +localVariableDescriptor.getName());
                                ProgramVariable locVar = new LocationVariable(
                                       new ProgramElementName(localVariableDescriptor.getName()),
                                       ji.getKeYJavaType(localVariableDescriptor.getType()));
                                progVarNS.add(locVar);
                            }
                        }

                        buffer.append("\\exists " + declaringType + " x; {"
                                + selfName + ":= x } \\<{method-frame( source="
                                + declaringType + ",this=" + selfName);
                        buffer.append(" ) : { " + wp.getName() + " = "
                                + wp.getExpression());
                        buffer.append(";} }\\>" + wp.getName() + " = TRUE");

                        Term term = ProblemLoader.parseTerm(buffer.toString(),
                                services, new Namespace(), progVarNS);

                        
                        listOfWatchpoints = listOfWatchpoints.append(term);
                    }
                }
                return listOfWatchpoints.size();
            }
        } catch (Throwable t) {
            System.out.println(t.toString());
            t.printStackTrace();
            return -1;
        }
    }

    /**
     * Gets the listOfTerm containing the WatchPoints. This method never returns
     * null. In case that there are no WatchPoints an empty ListOfTerm is
     * returned.
     * 
     * @return the list of WatchPoints as ListOfTerm
     */
    public ListOfTerm getListOfWatchpoints(Services services) {

        translateWatchpoints(services);
        assert listOfWatchpoints != null : "listOfWatchpoints is null";
        return listOfWatchpoints;
    }

}

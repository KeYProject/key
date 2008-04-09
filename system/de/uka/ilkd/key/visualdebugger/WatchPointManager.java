package de.uka.ilkd.key.visualdebugger;

import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.ListOfType;
import de.uka.ilkd.key.java.abstraction.SLListOfType;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.logic.ListOfTerm;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.SLListOfTerm;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.ProblemLoader;
import de.uka.ilkd.key.util.PositionWrapper;
import de.uka.ilkd.key.util.WatchpointUtil;

/**
 * The Class WatchPointManager keeps a list of all watchpoints.
 */
public class WatchPointManager {

    /** The watch points in a raw format. */
    private LinkedList<WatchPoint> watchPoints = new LinkedList<WatchPoint>();

    /** The watch points parsed as key data structures. */
    private ListOfTerm listOfWatchpoints;

    /** Local variables contained in the watchpoints, if there are any. */
    private static HashSet<SourceElement> localVariables = new HashSet<SourceElement>();
    private static HashSet<SourceElement> initiallyRenamedLocalVariables = new HashSet<SourceElement>();

    private static LinkedList<PositionWrapper> temporaryLocalVariables = new LinkedList<PositionWrapper>();

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
     * @return the count of translated WatchPoints
     */
    private int translateWatchpoints(Services services) {

        LinkedList<WatchPoint> watchpoints = getWatchPoints();
        listOfWatchpoints = SLListOfTerm.EMPTY_LIST;
        temporaryLocalVariables = new LinkedList<PositionWrapper>();

        try {
            assert (watchpoints != null) : "Watchpoints are NULL!";

            if (watchpoints.isEmpty()) {
                return 0;
            } else {

                Namespace progVarNS = new Namespace();

                final JavaInfo ji = services.getJavaInfo();

                for (int i = 0; i < watchpoints.size(); i++) {

                    WatchPoint wp = watchpoints.get(i);

                    if (wp.isEnabled()) {

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

                        if (wp.getLocalVariables() != null
                                && wp.getLocalVariables().size() > 0) {
                            translateLocalVariables(progVarNS, ji, wp);
                        }

                        listOfWatchpoints = listOfWatchpoints
                                .append(createWatchpointTerm(services,
                                        progVarNS, wp, declaringType, selfName));
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
     * @param services
     * @param progVarNS
     * @param wp
     * @param declaringType
     * @param selfName
     * @return
     */
    private Term createWatchpointTerm(Services services, Namespace progVarNS,
            WatchPoint wp, String declaringType, ProgramElementName selfName) {
        
        StringBuffer buffer = new StringBuffer();
        buffer.append("\\exists " + declaringType + " x; {" + selfName
                + ":= x } \\<{method-frame( source=" + declaringType + ",this="
                + selfName);
        buffer.append(" ) : { " + wp.getName() + " = " + wp.getExpression());
        buffer.append(";} }\\>" + wp.getName() + " = TRUE");

        Term term = ProblemLoader.parseTerm(buffer.toString(), services,
                new Namespace(), progVarNS);
        return term;
    }

    /**
     * @param progVarNS
     * @param ji
     * @param wp
     */
    private void translateLocalVariables(Namespace progVarNS,
            final JavaInfo ji, WatchPoint wp) {

        List<LocalVariableDescriptor> locVars = wp.getLocalVariables();
        List<String> parameterTypes = wp.getParameterTypes();
        ListOfType signature = SLListOfType.EMPTY_LIST;

        for (String type : parameterTypes) {
            signature = signature.append(ji.getKeYJavaType(type));
        }

        KeYJavaType classType = ji.getKeYJavaType(wp.getDeclaringType());
        ProgramMethod pm = ji.getProgramMethod(classType, wp.getMethod(),
                signature, classType);
        MethodVisitor pvc = new MethodVisitor(pm.getMethodDeclaration());
        pvc.start();
        HashMap<Integer, SourceElement> keyPositions = WatchpointUtil
                .valueToKey(pvc.result());
        System.out.println(keyPositions);

        for (LocalVariableDescriptor localVariableDescriptor : locVars) {

            SourceElement variableSpecification = keyPositions
                    .get(localVariableDescriptor.getPosition());

            temporaryLocalVariables.add(new PositionWrapper(pm,
                    localVariableDescriptor.getPosition()));
            localVariables.add(variableSpecification);
            VariableSpecification varspec = (VariableSpecification)variableSpecification;
//            LocationVariable locVar = new LocationVariable(
//                    new ProgramElementName(localVariableDescriptor.getName()),
//                    ji.getKeYJavaType(localVariableDescriptor.getType()));
            LocationVariable locVar = (LocationVariable) varspec.getProgramVariable();
            progVarNS.add(locVar);
            System.out.println(locVar.hashCode() + " ID " + locVar.id() + " " + locVar);
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

    public static HashSet<SourceElement> getLocalVariables() {
        return localVariables;
    }

    public static void setLocalVariables(HashSet<SourceElement> localVariables) {
        WatchPointManager.localVariables = localVariables;
    }

    public static LinkedList<PositionWrapper> getTemporaryLocalVariables() {
        return temporaryLocalVariables;
    }

    public static HashSet<SourceElement> getInitiallyRenamedLocalVariables() {
        return initiallyRenamedLocalVariables;
    }

    public static void setInitiallyRenamedLocalVariables(
            HashSet<SourceElement> initiallyRenamedLocalVariables) {
        WatchPointManager.initiallyRenamedLocalVariables = initiallyRenamedLocalVariables;
    }
    
}

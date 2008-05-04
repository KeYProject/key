package de.uka.ilkd.key.visualdebugger.watchpoints;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.ListOfType;
import de.uka.ilkd.key.java.abstraction.SLListOfType;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.ReferencePrefix;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.ProgramPrefix;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.ProblemLoader;

/**
 * The Class WatchPointManager keeps a list of all watchpoints.
 */
public class WatchPointManager {

    private static boolean watchPointsContainLocals;
    /** The watch points in a raw format. */
    private LinkedList<WatchPoint> watchPoints = new LinkedList<WatchPoint>();
    /**
     * Gets the watch points.
     * 
     * @return the watch points
     */
    private LinkedList<WatchPoint> getWatchPoints() {
        return watchPoints;
    }


    /**
     * Translates the WatchPoints into KeY data structures.
     * 
     * @return the count of translated WatchPoints
     */
    private int translateWatchpoints(Services services) {
    
        LinkedList<WatchPoint> watchpoints = getWatchPoints();
        watchPointsContainLocals = false;
    
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
                        while (progVarNS.lookup(selfName) != null) {
                            nameOfSelf = nameOfSelf.concat("Z");
                            selfName = new ProgramElementName(nameOfSelf);
                        }
    
                        ProgramVariable var_self = new LocationVariable(
                                selfName, ji.getKeYJavaType(declaringType));
                        System.out.println(var_self.id());
                        wp.setSelf(var_self);
                        ProgramVariable var_dummy = new LocationVariable(
                                new ProgramElementName(wp.getName()), services
                                        .getTypeConverter().getBooleanType());
                        progVarNS.addSafely(var_self);
                        progVarNS.addSafely(var_dummy);
    
                        if (wp.getLocalVariables() != null
                                && wp.getLocalVariables().size() > 0) {
                            translateLocalVariables(progVarNS, services, wp);
                            watchPointsContainLocals = true;
                        }
    
                        wp.setWatchpointTerm(createWatchpointTerm(services,
                                progVarNS, wp, declaringType, selfName));
                    }
                }
                return 1;
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
     * @return the watchpoint formula 
     */
    private Term createWatchpointTerm(Services services, Namespace progVarNS,
            WatchPoint wp, String declaringType, ProgramElementName selfName) {
        
        StringBuffer buffer = new StringBuffer();
        buffer.append("\\<{method-frame( source=" + declaringType + ",this="
                + selfName);
        buffer.append(" ) : { " + wp.getName() + " = " + wp.getExpression());
        buffer.append(";} }\\>" + wp.getName() + " = TRUE");
        
        return ProblemLoader.parseTerm(buffer.toString(), services,
                new Namespace(), progVarNS);

    }
    /**
     * @param progVarNS
     * @param services
     * @param wp
     */
    private void translateLocalVariables(Namespace progVarNS,
            final Services services, WatchPoint wp) {

        final JavaInfo ji = services.getJavaInfo();
        
        List<LocalVariableDescriptor> locVars = wp.getLocalVariables();
        List<String> parameterTypes = wp.getParameterTypes();
        ListOfType signature = SLListOfType.EMPTY_LIST;
    

        for (String type : parameterTypes) {
            signature = signature.append(ji.getKeYJavaType(type));
        }

        KeYJavaType classType = ji.getKeYJavaType(wp.getDeclaringType());
        ProgramMethod pm = ji.getProgramMethod(classType, wp.getMethod(),
                signature, classType);
        wp.setProgramMethod(pm);
        MethodVisitor pvc = new MethodVisitor(pm.getMethodDeclaration(), services);
        pvc.start();
        HashMap<Integer, SourceElement> keyPositions = WatchpointUtil
                .valueToKey(pvc.result());
        
        List<Integer> variablePositions = new LinkedList<Integer>();
        List<LocationVariable> orginialLocalVariables = new LinkedList<LocationVariable>();
        
        for (LocalVariableDescriptor localVariableDescriptor : locVars) {
            
            variablePositions.add(localVariableDescriptor.getPosition());
            
            SourceElement variableSpecification = keyPositions
                    .get(localVariableDescriptor.getPosition());
            
            VariableSpecification varspec = (VariableSpecification)variableSpecification;
            LocationVariable locVar = (LocationVariable) varspec.getProgramVariable();
            orginialLocalVariables.add(locVar);
            
            progVarNS.add(locVar);
            System.out.println(locVar.hashCode() + " ID " + locVar.id() + " " + locVar);
        }
        wp.setKeyPositions(variablePositions);
        wp.setOrginialLocalVariables(orginialLocalVariables);
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
     * Gets the list of WatchPoints. This method never returns
     * null. In case that there are no WatchPoints an empty ListOfTerm is
     * returned.
     * 
     * @return the list of WatchPoints as ListOfTerm
     */
    public LinkedList<WatchPoint> getListOfWatchpoints(Services services) {

        translateWatchpoints(services);
        return watchPoints;
    }

    public static boolean existsWatchPointContainingLocals() {
        return watchPointsContainLocals;
    }
}

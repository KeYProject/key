package de.uka.ilkd.key.visualdebugger;

import java.util.LinkedList;

import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.ListOfTerm;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.SLListOfTerm;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.ProblemLoader;

/**
 * The Class WatchPointManager keeps a list of all watchpoints.
 */
public class WatchPointManager {

    /** The watch points. */
    private LinkedList<WatchPoint> watchPoints = new LinkedList<WatchPoint>();
    private LinkedList<Integer> statements = new LinkedList<Integer>(); 
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

        System.out.println("translateWatchpoints()...");
        LinkedList<WatchPoint> watchpoints = getWatchPoints();
        listOfWatchpoints = SLListOfTerm.EMPTY_LIST;
        assert (watchpoints != null);

        if (watchpoints.isEmpty()) {
            System.out
                    .println("translateWatchpoints: No watches created so far");
            return 0;
        } else {

            Namespace progVarNS = new Namespace();

            final JavaInfo ji = services.getJavaInfo();

            for (int i = 0; i < watchpoints.size(); i++) {

                WatchPoint wp = watchpoints.get(i);

                if (wp.isEnabled()) {
                    StringBuffer buffer = new StringBuffer();
                    String typeOfSource = wp.getTypeOfSource();

                    String nameOfSelf = "self_XY";
                    ProgramElementName selfName = new ProgramElementName(
                            nameOfSelf);

                    // check namespace
                    while (services.getNamespaces().lookup(selfName) != null) {
                        nameOfSelf.concat("Z");
                        selfName = new ProgramElementName(nameOfSelf);
                    }

                    ProgramVariable var_self = new LocationVariable(selfName,
                            ji.getKeYJavaType(typeOfSource));
                    ProgramVariable var_dummy = new LocationVariable(
                            new ProgramElementName(wp.getName()), services
                                    .getTypeConverter().getBooleanType());
                    progVarNS.add(var_self);
                    progVarNS.add(var_dummy);

                    buffer.append("\\exists " + typeOfSource + " x; {"
                            + selfName + ":= x } \\<{method-frame( source="
                            + typeOfSource + ",this=" + selfName);
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

/** 
 * Utilities class
 */

package de.uka.ilkd.asmkey.unit;

import de.uka.ilkd.asmkey.parser.ast.AstUnit;
import de.uka.ilkd.asmkey.parser.ast.HashMapFromNameToAstUnit;
import de.uka.ilkd.key.logic.Name;

public class UnitUtil {

    public static ListOfUnit convertAndReverse(IteratorOfUnit it) {

	ListOfUnit list = SLListOfUnit.EMPTY_LIST;
	while(it.hasNext()) {
	    list = list.prepend(it.next());
	}
	return list;
    }

    public static HashMapFromNameToAstUnit createAstUnitMap(AstUnit[] units) {
	//HashMapFromNameToAstUnit map = new HashMapFromNameToAstUnit(units.length);
	HashMapFromNameToAstUnit map = new HashMapFromNameToAstUnit();

	for(int i = 0; i<units.length; i++) {
	    map.put(new Name(units[i].getUnitId().getText()), units[i]);
	}
	return map;
    }

    public static class EmptyUnitListener implements UnitListener {
	public void beginLogging() {}
	
	public void pauseLogging() {}
	
	public void stopLogging() {}
	
	public void loadingInitialLogEntry(String message, int major) {}
	
	public void loadingMajorLogEntry(String message, int minor) {}
	
	public void loadingMajorLogEntry(String message) {}
	
	public void loadingMinorLogEntry(String message) {}
	
	public void operationLogEntry(String message) {}
    }

}

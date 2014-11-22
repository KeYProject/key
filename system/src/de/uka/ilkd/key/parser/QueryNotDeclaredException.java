package de.uka.ilkd.key.parser;

import de.uka.ilkd.key.logic.Term;

/**
 * Thrown by KeYParser in case an undeclared query occurs. Prints out detailed 
 * information about the query that occured.
 *
 * @author Kai Wallisch <kai.wallisch@ira.uka.de>
 */
public class QueryNotDeclaredException extends NotDeclException {

    private String message;

    public QueryNotDeclaredException(String queryName, Term[] arguments, String source, int line, int column) {
        message = "Function or static query not declared.\n";
        message += "Query name: " + queryName + "\n";
        message += "Number of arguments: " + arguments.length + "\n";
        int i = 0;
        for (Term t : arguments) {
            message += "Argument " + (i++) + ": ";
            message += t.toString() + " (sort: " + t.sort() + ") " + "\n";
        }
        message += "Source (filename): " + source + "\n";
        message += "Line: " + line + "\n";
        message += "Column: " + column;
    }

    @Override
    public String getMessage() {
        return message;
    }
}

package de.uka.ilkd.key.logic.label;

import java.util.HashMap;
import java.util.Map;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.rule.label.TermLabelPolicy;
import de.uka.ilkd.key.rule.label.TermLabelRefactoring;
import de.uka.ilkd.key.rule.label.TermLabelUpdate;

/**
 * A {@link TermLabelState} is used to share information between participants
 * which manage {@link TermLabel}s during rule application. Participants are:
 * <ul>
 *    <li>{@link TermLabelPolicy}</li>
 *    <li>{@link TermLabelUpdate}</li>
 *    <li>{@link TermLabelRefactoring}</li>
 * </ul>
 * <p>
 * Exactly one {@link TermLabelState} instance is created in each
 * {@link Rule#apply(de.uka.ilkd.key.proof.Goal, de.uka.ilkd.key.java.Services, de.uka.ilkd.key.rule.RuleApp)}
 * implementation and passed to each performed {@link TermLabelManager} call
 * during rule application and thus passed to the participants.
 * @author Martin Hentschel
 */
public class TermLabelState {
   /**
    * Stores for each {@link TermLabel} {@link Name} the state.
    */
   private final Map<Name, Map<Object, Object>> labelStateMap = new HashMap<Name, Map<Object,Object>>();

   /**
    * Constructor.
    */
   public TermLabelState() {
   }
   
   /**
    * Return the state {@link Map} in which arbitrary key values pairs can be stored
    * for the given {@link TermLabel} {@link Name}.
    * @param termLabelName The {@link Name} of the {@link TermLabel}.
    * @return The {@link Map} used by the {@link TermLabel}s participants.
    */
   public Map<Object, Object> getLabelState(Name termLabelName) {
      synchronized (labelStateMap) {
         Map<Object, Object> result = labelStateMap.get(termLabelName);
         if (result == null) {
            result = new HashMap<Object, Object>();
            labelStateMap.put(termLabelName, result);
         }
         return result;
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String toString() {
      return "TermLabelState " + System.identityHashCode(this) + ": " + labelStateMap;
   }
}

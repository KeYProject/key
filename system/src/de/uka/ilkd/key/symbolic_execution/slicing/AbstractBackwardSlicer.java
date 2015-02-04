package de.uka.ilkd.key.symbolic_execution.slicing;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.SortedSet;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.NonTerminalProgramElement;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.expression.operator.CopyAssignment;
import de.uka.ilkd.key.java.reference.FieldReference;
import de.uka.ilkd.key.java.reference.ReferencePrefix;
import de.uka.ilkd.key.java.reference.ThisReference;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.util.Pair;

/**
 * Provides a basic implementation of backward slicing algorithms.
 * @author Martin Hentschel
 */
public abstract class AbstractBackwardSlicer extends AbstractSlicer {
   /**
    * {@inheritDoc}
    */
   @Override
   public ImmutableArray<Node> doSlicing(Node seedNode, ReferencePrefix seedLocation) {
      Set<ReferencePrefix> relevantLocations = null;
      List<Node> result = new LinkedList<Node>();
      Map<ReferencePrefix, SortedSet<ReferencePrefix>> oldAliases = null;
      while (seedNode != null && (relevantLocations == null || !relevantLocations.isEmpty())) {
         Pair<Map<ReferencePrefix, SortedSet<ReferencePrefix>>, ReferencePrefix> pair = analyzeSequent(seedNode);
         if (pair != null) { // Modality of interest
            SourceElement activeStatement = seedNode.getNodeInfo().getActiveStatement();
            Map<ReferencePrefix, SortedSet<ReferencePrefix>> aliases = pair.first;
            ReferencePrefix thisReference = pair.second;
            if (relevantLocations == null) {
               // Initialize relevant locations if required
               relevantLocations = new HashSet<ReferencePrefix>();
               relevantLocations.add(normalizeAlias(seedLocation, aliases, thisReference));
            }
            // Check if current node is part of the slice or not
            if (accept(seedNode, relevantLocations, aliases, thisReference, activeStatement)) {
               result.add(seedNode);
            }
            if (oldAliases != null) {
               // Update relevant locations if required
               if (activeStatement instanceof CopyAssignment) {
                  SourceElement originalTarget = ((CopyAssignment) activeStatement).getArguments().get(0);
                  ReferencePrefix relevantTarget = computeReferencePrefix(originalTarget);
                  ReferencePrefix normalizedPrefix = normalizeAlias(relevantTarget, aliases, thisReference);
                  relevantLocations = updateOutdatedLocations(relevantLocations, aliases, oldAliases, normalizedPrefix, thisReference);
               }
            }
            oldAliases = aliases;
         }
         seedNode = seedNode.parent();
      }
      return new ImmutableArray<Node>(result);
   }

   /**
    * Decides if the given {@link Node} is part of the slice or not.
    * @param node The {@link Node} to check.
    * @param relevantLocations The relevant locations.
    * @param aliases The available aliases.
    * @param thisReference The {@link ReferencePrefix} which is represented by {@code this} ({@link ThisReference}).
    * @param activeStatement The currently active statement.
    * @return {@code true} {@link Node} should be part of slice, {@code false} {@link Node} should not be part of slice.
    */
   protected abstract boolean accept(Node node, 
                                     Set<ReferencePrefix> relevantLocations, 
                                     Map<ReferencePrefix, SortedSet<ReferencePrefix>> aliases,
                                     ReferencePrefix thisReference,
                                     SourceElement activeStatement);

   /**
    * Updates the relevant locations.
    * @param read The {@link Expression} which provides new relevant locations.
    * @param relevantLocations The relevant locations to update.
    * @param aliases The available aliases.
    * @param thisReference The {@link ReferencePrefix} which is represented by {@code this} ({@link ThisReference}).
    * @param services The {@link Services} to use.
    */
   protected void updateRelevantLocations(final ProgramElement read, 
                                          final Set<ReferencePrefix> relevantLocations, 
                                          final Map<ReferencePrefix, SortedSet<ReferencePrefix>> aliases,
                                          final ReferencePrefix thisReference,
                                          final Services services) {
      ReferencePrefix relevantElement = computeReferencePrefix(read);
      if (relevantElement != null) {
         ReferencePrefix normalizedElement = normalizeAlias(relevantElement, aliases, thisReference);
         relevantLocations.add(normalizedElement);
      }
      else if (read instanceof NonTerminalProgramElement) {
         NonTerminalProgramElement ntpe = (NonTerminalProgramElement) read;
         for (int i = 0; i < ntpe.getChildCount(); i++) {
            updateRelevantLocations(ntpe.getChildAt(i), relevantLocations, aliases, thisReference, services);
         }
      }
   }

   /**
    * Updates the outdated locations. This means that locations with the given
    * prefix are replaced with another previously (old) available alternative.
    * @param oldLocationsToUpdate The locations to update.
    * @param newAliases The new aliases.
    * @param oldAliases The old aliases.
    * @param outdatedPrefix The prefix of outdated locations.
    * @param thisReference The {@link ReferencePrefix} which is represented by {@code this} ({@link ThisReference}).
    * @return The updated locations.
    */
   protected Set<ReferencePrefix> updateOutdatedLocations(Set<ReferencePrefix> oldLocationsToUpdate,
                                                          Map<ReferencePrefix, SortedSet<ReferencePrefix>> newAliases, 
                                                          Map<ReferencePrefix, SortedSet<ReferencePrefix>> oldAliases, 
                                                          ReferencePrefix outdatedPrefix,
                                                          ReferencePrefix thisReference) {
      // Ensure that at least one possibly outdated location is available.
      if (!oldLocationsToUpdate.isEmpty()) {
         // Ensure that alternatives are different
         SortedSet<ReferencePrefix> newAlternatives = newAliases.get(outdatedPrefix);
         if (newAlternatives == null) {
            newAlternatives = createSortedSet();
            newAlternatives.add(outdatedPrefix);
         }
         SortedSet<ReferencePrefix> oldAlternatives = oldAliases.get(outdatedPrefix);
         if (oldAlternatives == null) {
            oldAlternatives = createSortedSet();
            oldAlternatives.add(outdatedPrefix);
         }
         if (!newAlternatives.equals(oldAlternatives)) {
            // Compute old variables
            ImmutableList<ImmutableList<ProgramVariable>> newAlternativeVariables = ImmutableSLList.nil();
            for (ReferencePrefix newALternative : newAlternatives) {
               ImmutableList<ProgramVariable> variables = extractProgramVariables(newALternative, thisReference);
               newAlternativeVariables = newAlternativeVariables.prepend(variables);
            }
            // Compute new alternative
            ReferencePrefix newAlternative = findNewAlternative(oldAlternatives, newAlternatives);
            // Compute new locations
            Set<ReferencePrefix> newLocations = new HashSet<ReferencePrefix>();
            for (ReferencePrefix oldLocation : oldLocationsToUpdate) {
               ImmutableList<ProgramVariable> oldVariables = extractProgramVariables(oldLocation, thisReference);
               int commonPrefixLength = computeFirstCommonPrefixLength(newAlternativeVariables, oldVariables);
               if (commonPrefixLength >= 1) {
                  if (newAlternative != null) { // Otherwise the relevant location is dropped because it was not known before
                     if (commonPrefixLength == oldVariables.size()) {
                        newLocations.add(newAlternative);
                     }
                     else {
                        ImmutableList<ProgramVariable> oldRemainignVariables = oldVariables.take(commonPrefixLength);
                        FieldReference newFr = new FieldReference(oldRemainignVariables.head(), newAlternative);
                        oldRemainignVariables = oldRemainignVariables.take(1);
                        while (!oldRemainignVariables.isEmpty()) {
                           newFr = new FieldReference(oldRemainignVariables.head(), newFr);
                           oldRemainignVariables = oldRemainignVariables.take(1);
                        }
                        newLocations.add(newFr);
                     }
                  }
               }
               else {
                  newLocations.add(oldLocation); // Maintain location
               }
            }
            return newLocations;
         }
         else {
            return oldLocationsToUpdate;
         }
      }
      else {
         return oldLocationsToUpdate;
      }
   }
}

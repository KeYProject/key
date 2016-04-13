package de.uka.ilkd.key.symbolic_execution.slicing;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.SortedSet;

import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.NonTerminalProgramElement;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.expression.operator.CopyAssignment;
import de.uka.ilkd.key.java.reference.ReferencePrefix;
import de.uka.ilkd.key.java.reference.ThisReference;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicEquivalenceClass;

/**
 * Provides a basic implementation of backward slicing algorithms.
 * @author Martin Hentschel
 */
public abstract class AbstractBackwardSlicer extends AbstractSlicer {
   /**
    * {@inheritDoc}
    */
   @Override
   public ImmutableArray<Node> doSlicing(Node seedNode, Location seedLocation, ImmutableList<ISymbolicEquivalenceClass> sec) throws ProofInputException {
      final Services services = seedNode.proof().getServices();
      Set<Location> relevantLocations = null;
      List<Node> result = new LinkedList<Node>();
      Map<Location, SortedSet<Location>> oldAliases = null;
      Node previousChild = null;
      while (seedNode != null && (relevantLocations == null || !relevantLocations.isEmpty())) {
         SequentInfo info = analyzeSequent(seedNode, sec);
         if (info != null) { // Modality of interest
            SourceElement activeStatement = seedNode.getNodeInfo().getActiveStatement();
            Map<Location, SortedSet<Location>> aliases = info.getAliases();
            ReferencePrefix thisReference = info.getThisReference();
            if (relevantLocations == null) {
               // Initialize relevant locations if required
               relevantLocations = new HashSet<Location>();
               relevantLocations.add(normalizeAlias(services, seedLocation, info));
            }
            // Check if current node is part of the slice or not
            if (accept(seedNode, previousChild, services, relevantLocations, info, activeStatement)) {
               result.add(seedNode);
            }
            if (oldAliases != null) {
               try {
                  // Update relevant locations if required
                  if (activeStatement instanceof CopyAssignment) {
                     SourceElement originalTarget = ((CopyAssignment) activeStatement).getArguments().get(0);
                     ReferencePrefix relevantTarget = toReferencePrefix(originalTarget);
                     Location normalizedPrefix = normalizeAlias(services, relevantTarget, info);
                     relevantLocations = updateOutdatedLocations(services, relevantLocations, aliases, oldAliases, normalizedPrefix, thisReference);
                  }
               }
               catch (IllegalArgumentException e) {
                  // Nothing to do, expression with side effects is evaluated
               }
            }
            oldAliases = aliases;
         }
         previousChild = seedNode;
         seedNode = seedNode.parent();
      }
      return new ImmutableArray<Node>(result);
   }

   /**
    * Decides if the given {@link Node} is part of the slice or not.
    * @param node The {@link Node} to check.
    * @param previousChild The previously visited child {@link Node} or {@code null} the first time.
    * @param services The {@link Services} to use.
    * @param relevantLocations The relevant locations.
    * @param info The {@link SequentInfo} with the aliases and so on.
    * @param activeStatement The currently active statement.
    * @return {@code true} {@link Node} should be part of slice, {@code false} {@link Node} should not be part of slice.
    */
   protected abstract boolean accept(Node node, 
                                     Node previousChild,
                                     Services services,
                                     Set<Location> relevantLocations, 
                                     SequentInfo info,
                                     SourceElement activeStatement) throws ProofInputException;

   /**
    * Updates the relevant locations.
    * @param read The {@link Expression} which provides new relevant locations.
    * @param relevantLocations The relevant locations to update.
    * @param info The {@link SequentInfo} with the aliases and so on.
    * @param services The {@link Services} to use.
    */
   protected void updateRelevantLocations(final ProgramElement read, 
                                          final Set<Location> relevantLocations, 
                                          final SequentInfo info,
                                          final Services services) {
      ReferencePrefix relevantElement = toReferencePrefix(read);
      if (relevantElement != null) {
         Location normalizedElement = normalizeAlias(services, relevantElement, info);
         relevantLocations.add(normalizedElement);
      }
      else if (read instanceof NonTerminalProgramElement) {
         NonTerminalProgramElement ntpe = (NonTerminalProgramElement) read;
         for (int i = 0; i < ntpe.getChildCount(); i++) {
            updateRelevantLocations(ntpe.getChildAt(i), relevantLocations, info, services);
         }
      }
   }

   /**
    * Updates the outdated locations. This means that locations with the given
    * prefix are replaced with another previously (old) available alternative.
    * @param services The {@link Services} to use.
    * @param oldLocationsToUpdate The locations to update.
    * @param newAliases The new aliases.
    * @param oldAliases The old aliases.
    * @param outdatedPrefix The prefix of outdated locations.
    * @param thisReference The {@link ReferencePrefix} which is represented by {@code this} ({@link ThisReference}).
    * @return The updated locations.
    */
   protected Set<Location> updateOutdatedLocations(Services services,
                                                   Set<Location> oldLocationsToUpdate,
                                                   Map<Location, SortedSet<Location>> newAliases, 
                                                   Map<Location, SortedSet<Location>> oldAliases, 
                                                   Location outdatedPrefix,
                                                   ReferencePrefix thisReference) {
      // Ensure that at least one possibly outdated location is available.
      if (!oldLocationsToUpdate.isEmpty()) {
         // Ensure that alternatives are different
         SortedSet<Location> newAlternatives = newAliases.get(outdatedPrefix);
         if (newAlternatives == null) {
            newAlternatives = createSortedSet();
            newAlternatives.add(outdatedPrefix);
         }
         SortedSet<Location> oldAlternatives = oldAliases.get(outdatedPrefix);
         if (oldAlternatives == null) {
            oldAlternatives = createSortedSet();
            oldAlternatives.add(outdatedPrefix);
         }
         if (!newAlternatives.equals(oldAlternatives)) {
            // Compute old variables
            ImmutableList<ImmutableList<Access>> newAlternativeVariables = ImmutableSLList.nil();
            for (Location newALternative : newAlternatives) {
               newAlternativeVariables = newAlternativeVariables.prepend(newALternative.getAccesses());
            }
            // Compute new alternative
            Location newAlternative = findNewAlternative(oldAlternatives, newAlternatives);
            // Compute new locations
            Set<Location> newLocations = new HashSet<Location>();
            for (Location oldLocation : oldLocationsToUpdate) {
               ImmutableList<Access> oldVariables = oldLocation.getAccesses();
               int commonPrefixLength = computeFirstCommonPrefixLength(newAlternativeVariables, oldVariables);
               if (commonPrefixLength >= 1) {
                  if (newAlternative != null) { // Otherwise the relevant location is dropped because it was not known before
                     if (commonPrefixLength == oldVariables.size()) {
                        newLocations.add(newAlternative);
                     }
                     else {
                        ImmutableList<Access> oldRemainignVariables = oldVariables.take(commonPrefixLength);
                        ImmutableList<Access> newAccesses = newAlternative.getAccesses().append(oldRemainignVariables);
                        newLocations.add(new Location(newAccesses));
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

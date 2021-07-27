package de.uka.ilkd.key.symbolic_execution.model.impl;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionBlockStartNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.ITreeSettings;

/**
 * Provides a basic implementation of {@link IExecutionBlockStartNode}.
 * @author Martin Hentschel
 */
public abstract class AbstractExecutionBlockStartNode<S extends SourceElement> extends AbstractExecutionNode<S> implements IExecutionBlockStartNode<S> {
   /**
    * The up to know discovered completing {@link IExecutionNode}s.
    */
   private ImmutableList<IExecutionNode<?>> blockCompletions = ImmutableSLList.nil();

   /**
    * Defines if a block is or might be opened.
    */
   private boolean blockOpened = true;
   
   /**
    * Constructor.
    * @param settings The {@link ITreeSettings} to use.
    * @param proofNode The {@link Node} of KeY's proof tree which is represented by this {@link IExecutionNode}.
    */
   public AbstractExecutionBlockStartNode(ITreeSettings settings, Node proofNode) {
      super(settings, proofNode);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isBlockOpened() {
      return blockOpened;
   }

   /**
    * Defines if a block might be opened or not.
    * @param blockOpened {@code false} block is definitively not opened, {@code true} block is or might be opened.
    */
   public void setBlockOpened(boolean blockOpened) {
      this.blockOpened = blockOpened;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ImmutableList<IExecutionNode<?>> getBlockCompletions() {
      return blockCompletions;
   }
   
   /**
    * Removes the given block completion.
    * @param completion The block completion to be removed.
    * @author Anna Filighera
    */
   public void removeBlockCompletion(IExecutionNode<?> completion) {
      blockCompletions = blockCompletions.removeAll(completion);
   }
   
   /**
    * Registers the given {@link IExecutionNode}.
    * @param blockCompletion The {@link IExecutionNode} to register.
    */
   public void addBlockCompletion(IExecutionNode<?> blockCompletion) {
      if (blockCompletion != null && !blockCompletions.contains(blockCompletion)) {
         if (blockCompletion instanceof AbstractExecutionNode<?>) {
            blockCompletions = blockCompletions.append(blockCompletion);
         }
         else {
            throw new IllegalArgumentException("Unsupported block completion: " + blockCompletion);
         }
      }
   }
}

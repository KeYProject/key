package org.key_project.sed.core.model.memory;

import java.util.LinkedList;
import java.util.List;

import org.eclipse.debug.core.DebugException;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.ISEDMethodReturn;
import org.key_project.sed.core.model.ISEDThread;
import org.key_project.sed.core.model.impl.AbstractSEDMethodReturn;

/**
 * Implementation of {@link ISEDMethodReturn} that stores all
 * information in the memory.
 * @author Martin Hentschel
 */
public class SEDMemoryMethodReturn extends AbstractSEDMethodReturn implements ISEDMemoryStackFrameCompatibleDebugNode, ISEDMemoryDebugNode {
   /**
    * The contained child nodes.
    */
   private List<ISEDDebugNode> children = new LinkedList<ISEDDebugNode>();
   
   /**
    * The name of this debug node.
    */
   private String name;
   
   /**
    * The source name.
    */
   private String sourceName;

   /**
    * The line number.
    */
   private int lineNumber = -1;

   /**
    * The index of the start character.
    */
   private int charStart = -1;
   
   /**
    * The index of the end character.
    */
   private int charEnd = -1;
   
   /**
    * Constructor.
    * @param target The {@link ISEDDebugTarget} in that this method return is contained.
    * @param parent The parent in that this node is contained as child.
    * @param thread The {@link ISEDThread} in that this method return is contained.
    */
   public SEDMemoryMethodReturn(ISEDDebugTarget target, 
                                ISEDDebugNode parent, 
                                ISEDThread thread) {
      super(target, parent, thread);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getName() throws DebugException {
      return name;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public String getSourceName() {
      return sourceName;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public int getLineNumber() throws DebugException {
      return lineNumber;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public int getCharStart() throws DebugException {
      return charStart;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public int getCharEnd() throws DebugException {
      return charEnd;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ISEDDebugNode[] getChildren() throws DebugException {
      return children.toArray(new ISEDDebugNode[children.size()]);
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void addChild(ISEDDebugNode child) {
      if (child != null) {
         children.add(child);
      }
   }

   /**
    * {@inheritDoc}
    */   
   @Override
   public void removeChild(ISEDDebugNode child) {
      if (child != null) {
         children.remove(child);
      }
   }

   /**
    * {@inheritDoc}
    */   
   @Override
   public void addChild(int index, ISEDDebugNode child) {
      if (child != null) {
         children.add(index, child);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public int indexOfChild(ISEDDebugNode child) {
      if (child != null) {
         return children.indexOf(child);
      }
      else {
         return -1;
      }
   }
   
   /**
    * Sets the name of this node.
    * @param name the name to set.
    */
   public void setName(String name) {
      this.name = name;
   }

   /**
    * Sets the line number.
    * @param lineNumber The line number or {@code -1} if it is unknown.
    */
   public void setLineNumber(int lineNumber) {
      this.lineNumber = lineNumber;
   }

   /**
    * Sets the index of the start character.
    * @param charStart The index or {@code -1} if it is unknown.
    */
   public void setCharStart(int charStart) {
      this.charStart = charStart;
   }

   /**
    * Sets the index of the end character.
    * @param charEnd The index or {@code -1} if it is unknown.
    */
   public void setCharEnd(int charEnd) {
      this.charEnd = charEnd;
   }
   
   /**
    * Sets the source name.
    * @param sourceName The source name to set.
    */
   public void setSourceName(String sourceName) {
      this.sourceName = sourceName;
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * Changed visibility to public.
    * </p>
    */
   @Override
   public void setId(String id) {
      super.setId(id);
   }
}

/*******************************************************************************
 * Copyright (c) 2014 Karlsruhe Institute of Technology, Germany
 *                    Technical University Darmstadt, Germany
 *                    Chalmers University of Technology, Sweden
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Technical University Darmstadt - initial API and implementation and/or initial documentation
 *******************************************************************************/

package org.key_project.sed.core.model;

import org.eclipse.debug.core.DebugException;
import org.eclipse.debug.core.model.IBreakpoint;
import org.eclipse.debug.core.model.IStackFrame;
import org.key_project.sed.core.annotation.ISEAnnotation;
import org.key_project.sed.core.annotation.ISEAnnotationLink;
import org.key_project.sed.core.annotation.ISEAnnotationType;
import org.key_project.sed.core.model.event.ISEAnnotationLinkListener;
import org.key_project.sed.core.model.impl.AbstractSENode;
import org.key_project.sed.core.model.impl.AbstractSEStackFrameCompatibleDebugNode;

/**
 * A node and his sub interfaces forms the symbolic execution tree for
 * each thread. A node contains the available children.
 * <p>
 * The following concrete nodes are available
 * <ul>
 * <li>{@link ISEThread} (root node)</li>
 * <li>{@link ISEStatement} (single statement, e.g. {@code int x =  1 + 2;})</li>
 * <li>{@link ISEBranchStatement} (branch statement, e.g. {@code if(x >= 0)})</li>
 * <li>{@link ISEBranchCondition} (branch condition, e.g. {@code x < 0})</li>
 * <li>{@link ISEMethodCall} (method call, e.g. {@code foo()})</li>
 * <li>{@link ISEMethodReturn} (method return, e.g. {@code return 42})</li>
 * <li>{@link ISETermination} (termination, e.g. {@code <end>})</li>
 * <li>{@link ISEExceptionalTermination} (exceptional termination, e.g. {@code <uncaught java.lang.NullPointerException>})</li>
 * </ul>
 * </p>
 * <p>
 * Clients may implement this interface. It should not be directly instantiated.
 * It is recommended to instantiate always one of the provided sub interfaces
 * and to subclass from {@link AbstractSENode} or from
 * {@link AbstractSEStackFrameCompatibleDebugNode} if the sub interface
 * also extends {@link IStackFrame} for compatibility reasons with the
 * Eclipse debug API.
 * </p>
 * @author Martin Hentschel
 */
public interface ISENode extends ISEDebugElement {
   /**
    * Returns the contained children.
    * @return
    * @exception DebugException if this method fails.  Reasons include:
    * <ul><li>Failure communicating with the VM.  The DebugException's
    * status code contains the underlying exception responsible for
    * the failure.</li>
    */
   public ISENode[] getChildren() throws DebugException;
   
   /**
    * Checks if children are available.
    * @return {@code true} children are available, {@code false} children are not available.
    * @throws DebugException Occurred Exception
    */
   public boolean hasChildren() throws DebugException;
   
   /**
    * Returns the {@link ISEThread} in that this {@link ISENode} is contained 
    * as child. An {@link ISEThread} returns itself.
    * @return The {@link ISEThread}.
    * @throws DebugException if this method fails.  Reasons include:
    * <ul><li>Failure communicating with the VM.  The DebugException's
    * status code contains the underlying exception responsible for
    * the failure.</li>
    */
   public ISEThread getThread() throws DebugException;
   
   /**
    * Returns the parent in that this node is contained as child.
    * @return The parent {@link ISENode} or {@code null} if it is the root of the symbolic execution tree.
    * @throws DebugException DebugException if this method fails.  Reasons include:
    * <ul><li>Failure communicating with the VM.  The DebugException's
    * status code contains the underlying exception responsible for
    * the failure.</li>
    */
   public ISENode getParent() throws DebugException;
   
   /**
    * Returns a human readable name.
    * @return The name of this node.
    * @throws DebugException DebugException if this method fails.  Reasons include:
    * <ul><li>Failure communicating with the VM.  The DebugException's
    * status code contains the underlying exception responsible for
    * the failure.</li>
    */
   public String getName() throws DebugException;
   
   /**
    * Returns a human readable node type name.
    * @return The human readable node type.
    * @throws DebugException DebugException if this method fails.  Reasons include:
    * <ul><li>Failure communicating with the VM.  The DebugException's
    * status code contains the underlying exception responsible for
    * the failure.</li>
    */
   public String getNodeType() throws DebugException; 
   
   /**
    * Returns a human readable path condition to the current node.
    * @return The human readable path condition to the current node.
    * @throws DebugException DebugException if this method fails.  Reasons include:
    * <ul><li>Failure communicating with the VM.  The DebugException's
    * status code contains the underlying exception responsible for
    * the failure.</li>
    */
   public String getPathCondition() throws DebugException;
   
   /**
    * Returns the method call stack.
    * @return The method call stack.
    * @throws DebugException DebugException if this method fails.  Reasons include:
    * <ul><li>Failure communicating with the VM.  The DebugException's
    * status code contains the underlying exception responsible for
    * the failure.</li>
    */
   public ISENode[] getCallStack() throws DebugException;
   
   /**
    * Adds the given {@link ISEAnnotationLink} to this node.
    * @param link The {@link ISEAnnotationLink} to add.
    */
   public void addAnnotationLink(ISEAnnotationLink link);
   
   /**
    * Removes the given {@link ISEAnnotationLink} from this node.
    * @param link The {@link ISEAnnotationLink} to remove.
    */
   public void removeAnnotationLink(ISEAnnotationLink link);
   
   /**
    * Returns all contained {@link ISEAnnotationLink}s.
    * @return All contained {@link ISEAnnotationLink}s.
    */
   public ISEAnnotationLink[] getAnnotationLinks();
   
   /**
    * Returns all contained {@link ISEAnnotationLink}s of the given {@link ISEAnnotationType}.
    * @param type The {@link ISEAnnotationType}.
    * @return All contained {@link ISEAnnotationLink}s of the given {@link ISEAnnotationType}
    */
   public ISEAnnotationLink[] getAnnotationLinks(ISEAnnotationType type);
   
   /**
    * Returns all {@link ISEAnnotation} referenced by {@link ISEAnnotationLink}s
    * in the order they are defined in the {@link ISEDebugTarget}.
    * @return The used {@link ISEAnnotation}s.
    */
   public ISEAnnotation[] computeUsedAnnotations();
   
   /**
    * Checks if the given {@link ISEAnnotationLink} is contained in this node.
    * @param link The {@link ISEAnnotationLink} to check.
    * @return {@code true} the {@link ISEAnnotationLink} is contained in this node, {@code false} the {@link ISEAnnotationLink} is not contained.
    */
   public boolean containsAnnotationLink(ISEAnnotationLink link);
   
   /**
    * Adds the given {@link ISEAnnotationLinkListener}.
    * @param l The {@link ISEAnnotationLinkListener} to add.
    */
   public void addAnnotationLinkListener(ISEAnnotationLinkListener l);
   
   /**
    * Removes the given {@link ISEAnnotationLinkListener}.
    * @param l The {@link ISEAnnotationLinkListener} to remove.
    */
   public void removeAnnotationLinkListener(ISEAnnotationLinkListener l);
   
   /**
    * Returns all {@link IBreakpoint}s which are fulfilled in this {@link ISENode}.
    * @return The fulfilled {@link IBreakpoint}s in this {@link ISENode}.
    */
   public IBreakpoint[] computeHitBreakpoints() throws DebugException;
   
   /**
    * Checks if constraints are considered at this symbolic execution tree node.
    * @return {@code true} constraints available, {@code false} constraints are not available.
    * @throws DebugException Occurred Exception.
    */
   public boolean hasConstraints() throws DebugException;
   
   /**
    * Returns all constraints which are considered at this symbolic execution tree node.
    * @return All constraints which are considered at this symbolic execution tree node.
    * @throws DebugException Occurred Exception.
    */
   public ISEConstraint[] getConstraints() throws DebugException;
   
   /**
    * Returns the conditions under which an {@link ISEGroupable} {@link ISENode} is completed by this {@link ISENode}.
    * <p>
    * The conditions are ordered by the occurrence in the tree. 
    * This means that the node at the second index is a parent or grand parent of the node at the first index and so on.
    * @return The conditions under which an {@link ISEGroupable} {@link ISENode} is completed by this {@link ISENode}.
    * @exception DebugException if this method fails.  Reasons include:
    * <ul><li>Failure communicating with the VM.  The DebugException's
    * status code contains the underlying exception responsible for
    * the failure.</li>
    */
   public ISEBranchCondition[] getGroupStartConditions() throws DebugException;
   
   /**
    * Returns the inner most visible group start condition.
    * @return The inner most visible group start condition or {@code null} if not available.
    * @exception DebugException if this method fails.  Reasons include:
    * <ul><li>Failure communicating with the VM.  The DebugException's
    * status code contains the underlying exception responsible for
    * the failure.</li>
    */
   public ISEBranchCondition getInnerMostVisibleGroupStartCondition() throws DebugException;
   
   /**
    * Returns the condition under which the given {@link ISENode} is completed by this {@link ISENode}.
    * @return The condition under which the given {@link ISENode} is completed by this {@link ISENode}.
    * @exception DebugException if this method fails.  Reasons include:
    * <ul><li>Failure communicating with the VM.  The DebugException's
    * status code contains the underlying exception responsible for
    * the failure.</li>
    */
   public ISEBranchCondition getGroupStartCondition(ISENode startNode) throws DebugException;
}
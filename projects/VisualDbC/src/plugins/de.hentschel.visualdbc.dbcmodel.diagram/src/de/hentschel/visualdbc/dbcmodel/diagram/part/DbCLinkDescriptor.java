/*******************************************************************************
 * Copyright (c) 2013 Karlsruhe Institute of Technology, Germany 
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

package de.hentschel.visualdbc.dbcmodel.diagram.part;

import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.gmf.runtime.emf.core.util.EObjectAdapter;
import org.eclipse.gmf.runtime.emf.type.core.IElementType;

/**
 * @generated
 */
public class DbCLinkDescriptor extends DbCNodeDescriptor {

   /**
    * @generated
    */
   private EObject mySource;

   /**
    * @generated
    */
   private EObject myDestination;

   /**
    * @generated
    */
   private IAdaptable mySemanticAdapter;

   /**
    * @generated
    */
   private DbCLinkDescriptor(EObject source, EObject destination,
         EObject linkElement, int linkVID) {
      super(linkElement, linkVID);
      mySource = source;
      myDestination = destination;
   }

   /**
    * @generated
    */
   public DbCLinkDescriptor(EObject source, EObject destination,
         IElementType elementType, int linkVID) {
      this(source, destination, (EObject) null, linkVID);
      final IElementType elementTypeCopy = elementType;
      mySemanticAdapter = new IAdaptable() {
         public Object getAdapter(Class adapter) {
            if (IElementType.class.equals(adapter)) {
               return elementTypeCopy;
            }
            return null;
         }
      };
   }

   /**
    * @generated
    */
   public DbCLinkDescriptor(EObject source, EObject destination,
         EObject linkElement, IElementType elementType, int linkVID) {
      this(source, destination, linkElement, linkVID);
      final IElementType elementTypeCopy = elementType;
      mySemanticAdapter = new EObjectAdapter(linkElement) {
         public Object getAdapter(Class adapter) {
            if (IElementType.class.equals(adapter)) {
               return elementTypeCopy;
            }
            return super.getAdapter(adapter);
         }
      };
   }

   /**
    * @generated
    */
   public EObject getSource() {
      return mySource;
   }

   /**
    * @generated
    */
   public EObject getDestination() {
      return myDestination;
   }

   /**
    * @generated
    */
   public IAdaptable getSemanticAdapter() {
      return mySemanticAdapter;
   }

}
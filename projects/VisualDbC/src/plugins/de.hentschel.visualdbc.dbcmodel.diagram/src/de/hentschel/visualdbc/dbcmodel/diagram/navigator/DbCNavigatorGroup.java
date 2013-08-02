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

package de.hentschel.visualdbc.dbcmodel.diagram.navigator;

import java.util.Collection;
import java.util.LinkedList;

/**
 * @generated
 */
public class DbCNavigatorGroup extends DbCAbstractNavigatorItem {

   /**
    * @generated
    */
   private String myGroupName;

   /**
    * @generated
    */
   private String myIcon;

   /**
    * @generated
    */
   private Collection myChildren = new LinkedList();

   /**
    * @generated
    */
   DbCNavigatorGroup(String groupName, String icon, Object parent) {
      super(parent);
      myGroupName = groupName;
      myIcon = icon;
   }

   /**
    * @generated
    */
   public String getGroupName() {
      return myGroupName;
   }

   /**
    * @generated
    */
   public String getIcon() {
      return myIcon;
   }

   /**
    * @generated
    */
   public Object[] getChildren() {
      return myChildren.toArray();
   }

   /**
    * @generated
    */
   public void addChildren(Collection children) {
      myChildren.addAll(children);
   }

   /**
    * @generated
    */
   public void addChild(Object child) {
      myChildren.add(child);
   }

   /**
    * @generated
    */
   public boolean isEmpty() {
      return myChildren.size() == 0;
   }

   /**
    * @generated
    */
   public boolean equals(Object obj) {
      if (obj instanceof de.hentschel.visualdbc.dbcmodel.diagram.navigator.DbCNavigatorGroup) {
         de.hentschel.visualdbc.dbcmodel.diagram.navigator.DbCNavigatorGroup anotherGroup = (de.hentschel.visualdbc.dbcmodel.diagram.navigator.DbCNavigatorGroup) obj;
         if (getGroupName().equals(anotherGroup.getGroupName())) {
            return getParent().equals(anotherGroup.getParent());
         }
      }
      return super.equals(obj);
   }

   /**
    * @generated
    */
   public int hashCode() {
      return getGroupName().hashCode();
   }

}
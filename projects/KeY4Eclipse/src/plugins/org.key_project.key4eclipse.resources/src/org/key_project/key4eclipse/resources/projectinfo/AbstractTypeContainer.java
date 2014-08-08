package org.key_project.key4eclipse.resources.projectinfo;

import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import org.eclipse.core.runtime.Assert;

/**
 * Provides the basic functionality to maintain types as known by KeY.
 * @author Martin Hentschel
 */
public abstract class AbstractTypeContainer {
   /**
    * The {@link ProjectInfo} in which this {@link PackageInfo} is part of.
    */
   private final ProjectInfo projectInfo;
   
   /**
    * The contained {@link TypeInfo}s.
    */
   private final List<TypeInfo> typesList = new LinkedList<TypeInfo>();
   
   /**
    * The contained {@link TypeInfo}s for quick access by their names.
    */
   private final Map<String, TypeInfo> typesMap = new HashMap<String, TypeInfo>();
   
   /**
    * Constructor.
    * @param projectInfo The {@link ProjectInfo} in which this {@link PackageInfo} is part of.
    */
   public AbstractTypeContainer(ProjectInfo projectInfo) {
      Assert.isNotNull(projectInfo);
      this.projectInfo = projectInfo;
   }

   /**
    * Adds the given {@link TypeInfo} at the given index.
    * @param type The {@link TypeInfo} to add.
    * @param index The index to add {@link TypeInfo} at.
    */
   public void addType(TypeInfo type, int index) {
      if (type != null) {
         typesMap.put(type.getName(), type);
         typesList.add(index, type);
         projectInfo.mapResource(type.getFile(), type);
         projectInfo.fireTypeAdded(this, type, index);
      }
   }

   /**
    * Returns all contained {@link TypeInfo}s.
    * @return All contained {@link TypeInfo}s.
    */
   public Collection<TypeInfo> getTypes() {
      return Collections.unmodifiableList(typesList);
   }
   
   /**
    * Searches the {@link TypeInfo} with the given name.
    * @param name The name.
    * @return The found {@link TypeInfo} or {@code null} if not available.
    */
   public TypeInfo getType(String name) {
      return typesMap.get(name);
   }

   /**
    * Removes all given {@link TypeInfo}s.
    * @param types The {@link TypeInfo}s to remove.
    */
   public void removeTypes(Collection<TypeInfo> types) {
      if (types != null) {
         for (TypeInfo type : types) {
            typesMap.remove(type.getName());
            projectInfo.unmapResource(type.getFile(), type);
         }
         typesList.removeAll(types);
         projectInfo.fireTypesRemoved(this, types);
      }
   }

   /**
    * Counts the contained {@link TypeInfo}s.
    * @return The number of contained {@link TypeInfo}s.
    */
   public int countTypes() {
      return typesMap.size();
   }

   /**
    * Returns the {@link TypeInfo} at the given index.
    * @param index The index of the requested {@link TypeInfo}.
    * @return The {@link TypeInfo} at the given index.
    */
   public TypeInfo getType(int index) {
      return typesList.get(index);
   }

   /**
    * Returns the index of the given {@link TypeInfo}.
    * @param method The {@link TypeInfo} for which its index is requested.
    * @return The index of the given {@link TypeInfo} or {@code -1} if not contained.
    */
   public int indexOfType(TypeInfo type) {
      return typesList.indexOf(type);
   }

   /**
    * Returns the {@link ProjectInfo} in which this {@link PackageInfo} is part of.
    * @return The {@link ProjectInfo} in which this {@link PackageInfo} is part of.
    */
   public ProjectInfo getProjectInfo() {
      return projectInfo;
   }
}

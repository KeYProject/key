package org.key_project.jmlediting.core.profile;

import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.ResourcesPlugin;
import org.key_project.jmlediting.core.profile.syntax.IKeyword;
import org.key_project.jmlediting.core.profile.syntax.IKeywordSort;
import org.key_project.jmlediting.core.profile.syntax.user.IUserDefinedKeywordContentDescription;

public class JMLProfileHelper {

   public static IKeyword findKeyword(final IJMLProfile profile,
         final String keyword) {
      return findKeyword(profile.getSupportedKeywords(), keyword);
   }

   public static IKeyword findKeyword(
         final Iterable<? extends IKeyword> keywords, final String keyword) {
      IKeyword foundKeyword = null;
      for (final IKeyword availableKeyword : keywords) {
         if (availableKeyword.getKeywords().contains(keyword)) {
            foundKeyword = availableKeyword;
            break;
         }
      }
      return foundKeyword;
   }

   /**
    * Get a filtered set of {@link IKeyword}, e.g. to propose only a subset of
    * {@link IKeyword}
    *
    * @param profile
    *           the {@link IJMLProfile} to get the {@link IKeyword} from
    * @param clazz
    *           the Class extending from {@link IKeyword} to filter
    * @param <T>
    *           the type of the filtered keywords
    * @return the filtered Set of {@link IKeyword} all Assignable from clazz
    */
   @SuppressWarnings("unchecked")
   public static <T extends IKeyword> Set<T> filterKeywords(
         final IJMLProfile profile, final Class<T> clazz) {
      if (clazz == null) {
         throw new IllegalArgumentException(
               "The class is not allowed to be null");
      }
      final Set<T> result = new HashSet<T>();
      for (final IKeyword keyword : profile.getSupportedKeywords()) {
         if (clazz.isAssignableFrom(keyword.getClass())) {
            result.add((T) keyword);
         }
      }
      return Collections.unmodifiableSet(result);
   }

   /**
    * Get a filtered set of {@link IKeyword} which are sub sorts of the given
    * one.
    *
    * @param profile
    *           the {@link IJMLProfile} to get the {@link IKeyword} from
    * @param sort
    *           the sort to filter by
    * @return the filtered Set of {@link IKeyword} which are sub sorts of sorts
    */
   public static Set<IKeyword> filterKeywords(final IJMLProfile profile,
         final IKeywordSort sort) {
      if (sort == null) {
         throw new IllegalArgumentException("Sort is not allowed to be null");
      }
      final Set<IKeyword> result = new HashSet<IKeyword>();
      for (final IKeyword keyword : profile.getSupportedKeywords()) {
         if (sort.covers(keyword.getSort())) {
            result.add(keyword);
         }
      }
      return Collections.unmodifiableSet(result);

   }

   public static IUserDefinedKeywordContentDescription getDescriptionById(
         final String id, final IJMLProfile profile) {
      for (final IUserDefinedKeywordContentDescription descr : profile
            .getSupportedContentDescriptions()) {
         if (descr.getId().equals(id)) {
            return descr;
         }
      }
      return null;
   }

   /**
    * Returns a set of projects of the current workspace, which used the given
    * profile.
    *
    * @param profile
    *           the profile to query for projects
    * @return a non null set of projects using the given profile
    */
   public static Set<IProject> getProjectsUsingProfile(final IJMLProfile profile) {
      final Set<IProject> affectedProjects = new HashSet<IProject>();
      for (final IProject project : ResourcesPlugin.getWorkspace().getRoot()
            .getProjects()) {
         if (JMLPreferencesHelper.getProjectActiveJMLProfile(project) == profile) {
            affectedProjects.add(project);
         }
      }
      return affectedProjects;
   }

   public static Set<IProject> getProjectsUsingWorkspaceProfile() {
      final Set<IProject> affectedProjects = new HashSet<IProject>();
      for (final IProject project : ResourcesPlugin.getWorkspace().getRoot()
            .getProjects()) {
         if (JMLPreferencesHelper.getProjectJMLProfile(project) == null) {
            affectedProjects.add(project);
         }
      }
      return affectedProjects;
   }
}

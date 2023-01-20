/*
 * @(#)Group.java	1.8 00/02/02
 *
 * Copyright 1997-2000 Sun Microsystems, Inc. All Rights Reserved.
 * 
 * This software is the proprietary information of Sun Microsystems, Inc.  
 * Use is subject to license terms.
 * 
 */



import com.sun.tools.doclets.*;
import com.sun.javadoc.*;
import java.util.*;

/**
 * Process and manage grouping of packages, as specified by "-group" option on
 * the command line. 
 * <p>
 * For example, if user has used "-group option as
 * -group "Core Packages" "java.*" -group "CORBA Packages" "org.omg.*", then  
 * the packages specified on the command line will be grouped according to their
 * names starting with either "java." or "org.omg.". All the other packages 
 * which do not fall in the user given groups, are grouped in default group,
 * named as either "Other Packages" or "Packages" depending upon if "-group" 
 * option used or not at all used respectively. 
 * </p>
 * <p> 
 * Also the packages are grouped according to the longest possible match of
 * their names with the grouping information provided. For example, if there
 * are two groups, like -group "Lang" "java.lang" and -group "Core" "java.*", 
 * will put the package java.lang in the group "Lang" and not in group "Core".
 * </p>
 *
 * @author Atul M Dambalkar
 */
public class Group {

    /**
     * Map of regular expressions with the corresponding group name.
     */
    private static Map regExpGroupMap = new HashMap();

    /**
     * List of regular expressions sorted according to the length. Regular 
     * expression with longest length will be first in the sorted order.
     */
    private static List sortedRegExpList = new ArrayList();

    /**
     * List of group names in the same order as given on the command line.
     */
    private static List groupList = new ArrayList();

    /**
     * Map of non-regular expressions(possible package names) with the 
     * corresponding group name.
     */
    private static Map pkgNameGroupMap = new HashMap();

    /**
     * Since we need to sort the keys in the reverse order(longest key first),
     * the compare method in the implementing class is doing the reverse
     * comparison.
     */
    private static class MapKeyComparator implements Comparator {
        public int compare(Object key1, Object key2) {
            return ((String)key2).length() - ((String)key1).length();
        }
    }
     
    /**       
     * Depending upon the format of the package name provided in the "-group"
     * option, generate two separate maps. There will be a map for mapping  
     * regular expression(only meta character allowed is '*' and that is at the
     * end of the regular expression) on to the group name. And another map
     * for mapping (possible) package names(if the name format doesen't contain
     * meta character '*', then it is assumed to be a package name) on to the 
     * group name. This will also sort all the regular expressions found in the 
     * reverse order of their lengths, i.e. longest regular expression will be
     * first in the sorted list.
     *
     * @param groupname       The name of the group from -group option.
     * @param pkgNameFormList List of the package name formats.
     * @param reporter        Error reporter object.
     */
    public static boolean checkPackageGroups(String groupname, 
                                             String pkgNameFormList,
                                             DocErrorReporter reporter) {
        StringTokenizer strtok = new StringTokenizer(pkgNameFormList, ":");
        if (groupList.contains(groupname)) {
            reporter.printError(getText("doclet.Groupname_already_used", 
                                         groupname));
            return false;
        }
        groupList.add(groupname);
        while (strtok.hasMoreTokens()) {
            String id = strtok.nextToken();
            if (id.length() == 0) {
                reporter.printError(getText("doclet.Error_in_packagelist", 
                                             groupname, pkgNameFormList));
                return false;
            }
            if (id.endsWith("*")) {
                id = id.substring(0, id.length() - 1);
                if (foundGroupFormat(regExpGroupMap, id, reporter)) {
                    return false;
                } 
                regExpGroupMap.put(id, groupname);
                sortedRegExpList.add(id);
            } else {
                if (foundGroupFormat(pkgNameGroupMap, id, reporter)) {
                    return false;
                } 
                pkgNameGroupMap.put(id, groupname);
            }
        }
        Collections.sort(sortedRegExpList, new MapKeyComparator());
        return true;
    }

    /**
     * Search if the given map has given the package format.
     *
     * @return true if package name format found in the map, else false.
     * @param map Map to be searched.
     * @param pkgFormat The pacakge format to search.
     * @param reporter Error reporter object.
     */
    static boolean foundGroupFormat(Map map, String pkgFormat,
                                    DocErrorReporter reporter) {
        if (map.containsKey(pkgFormat)) { 
            reporter.printError(getText("doclet.Same_package_name_used", 
                                         pkgFormat));
            return true;
        }
        return false;
    }

    /** 
     * This is needed since Arrays.asList() raises
     * UnSupportedOperationException.
     */
    static List asList(Object[] arr) {
        List list = new ArrayList();
        for (int i = 0; i < arr.length; i++) {
            list.add(arr[i]);
        }
        return list;
    }

    /**
     * Group the packages according the grouping information provided on the
     * command line. Given a list of packages, search each package name in 
     * regular expression map as well as package name map to get the 
     * corresponding group name. Create another map with mapping of group name
     * to the package list, which will fall under the specified group. If any
     * package doesen't belong to any specified group on the comamnd line, then 
     * a new group named "Other Packages" will be created for it. If there are 
     * no groups found, in other words if "-group" option is not at all used, 
     * then all the packages will be grouped under group "Packages".
     * 
     * @param packages Packages specified on the command line.
     */
    public static Map groupPackages(PackageDoc[] packages) {
        Map groupPackageMap = new HashMap();
        String defaultGroupName = 
            (pkgNameGroupMap.isEmpty() && regExpGroupMap.isEmpty())? 
                getText("doclet.Packages") :
                getText("doclet.Other_Packages");
        // if the user has not used the default group name, add it
        if (!groupList.contains(defaultGroupName)) {
            groupList.add(defaultGroupName);
        }
        for (int i = 0; i < packages.length; i++) {
            PackageDoc pkg = packages[i];
            String pkgName = pkg.name();
            String groupName = (String)pkgNameGroupMap.get(pkgName);
            // if this package is not explictly assigned to a group,
            // try matching it to group specified by regular expression 
            if (groupName == null) {
                groupName = regExpGroupName(pkgName);
            }
            // if it is in neither group map, put it in the default
            // group
            if (groupName == null) {
                groupName = defaultGroupName;
            }
            getPkgList(groupPackageMap, groupName).add(pkg);
        }
        return groupPackageMap;
    }
     
    /**
     * Search for package name in the sorted regular expression 
     * list, if found return the group name.  If not, return null.
     * 
     * @param pkgName Name of package to be found in the regular 
     * expression list.
     */
    static String regExpGroupName(String pkgName) { 
        for (int j = 0; j < sortedRegExpList.size(); j++) {
            String regexp = (String)sortedRegExpList.get(j); 
            if (pkgName.startsWith(regexp)) {
                return (String)regExpGroupMap.get(regexp);
            } 
        }
        return null;
    }

    /**
     * For the given group name, return the package list, on which it is mapped.
     * Create a new list, if not found.
     * 
     * @param map Map to be searched for gorup name.
     * @param groupname Group name to search.
     */
    static List getPkgList(Map map, String groupname) {
        List list = (List)map.get(groupname);
        if (list == null) {
            list = new ArrayList();
            map.put(groupname, list);
        }
        return list;
    }

    /**
     * Return the list of groups, in the same order as specified on the command 
     * line.
     */
    public static List getGroupList() {
        return groupList;
    }
    
    /**                 
     * Retireve the message string from the resource bundle.
     *
     * @param text Key for the resource message string.
     * @param arg1 Argument to be substituted in the resource message string.
     * @param arg2 Argument to be substituted in the resource message string.
     */
    private static String getText(String text, String arg1, String arg2) {
        return Standard.configuration().standardmessage.getText(text, 
                                                                arg1, arg2);
    }   

    /**                 
     * Retireve the message string from the resource bundle.
     *
     * @param text Key for the resource message string.
     * @param arg  Argument to be substituted in the resource message string.
     */
    private static String getText(String text, String arg) {
        return Standard.configuration().standardmessage.getText(text, arg);
    }   

    /**                 
     * Retireve the message string from the resource bundle.
     *
     * @param text Key for the resource message string.
     */
    private static String getText(String text) {
        return Standard.configuration().standardmessage.getText(text);
    }   
} 
        


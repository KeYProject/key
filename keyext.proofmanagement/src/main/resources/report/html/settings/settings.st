<table>
    <thead class="tableHead">
    <tr>
        <th>ID</th>
        $cd.choiceNames:{c |<th>$c$</th>
        }$
    </tr>
    </thead>
    <tbody>
        $cd.shortChoices2Id.entrySet:{entry | $choices(names=cd.choiceNames,entry=entry)$}$
    </tbody>
</table>

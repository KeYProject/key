<li>
    $if(dir.getChildren().isEmpty())$
        dir.getChildren():{f |
        <span class="caret">$dir.content$</span>
            <ul class="nested">
                $directory(f)$
            </ul>
        }
    $else$
        $dir.content$
    $endif$
</li>
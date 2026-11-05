// Every story, in sidebar order.

use lib::story {Book.Story}
use lib::stories::foundations {foundation_stories}
use lib::stories::controls {control_stories}
use lib::stories::display {display_stories}
use lib::stories::navigation {navigation_stories}

pub def Book.all_stories : List Book.Story :=
    List.append foundation_stories
        (List.append control_stories (List.append display_stories navigation_stories))

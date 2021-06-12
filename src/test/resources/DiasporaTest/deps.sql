-- additional dependencies, one per line
-- q1; q2;
-- --> q1 \subseteq q2

SELECT users.id FROM users; SELECT owner_id FROM people;

-- reshare_constraints: (assert (forall (posts tuple t) (=> (and (t in posts) (= t.type C_RESHARE)) (and (= t.public 1) (exists (posts tuple tr) (and (tr in posts) (= t.root_guid tr.guid) (= tr.public 1)))))))
SELECT posts.guid FROM posts WHERE posts.type = 'Reshare' AND posts.public = 0; SELECT posts.guid FROM posts WHERE FALSE;
SELECT posts.root_guid FROM posts WHERE posts.type = 'Reshare'; SELECT posts.guid FROM posts WHERE posts.public = 1;

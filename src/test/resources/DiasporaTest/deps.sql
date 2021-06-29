-- additional dependencies, one per line
-- q1; q2;
-- --> q1 \subseteq q2

SELECT users.id FROM users; SELECT owner_id FROM people;

-- reshare_constraints: (assert (forall (posts tuple t) (=> (and (t in posts) (= t.type C_RESHARE)) (and (= t.public 1) (exists (posts tuple tr) (and (tr in posts) (= t.root_guid tr.guid) (= tr.public 1)))))))
-- In our current implementation, we must write `posts.public <> 1` instead of `posts.public = 0` because we model
-- a Boolean field as an integer and don't constrain its value to be {0, 1}.
SELECT posts.guid FROM posts WHERE posts.type = 'Reshare' AND posts.public <> 1; SELECT posts.guid FROM posts WHERE FALSE;
SELECT posts.root_guid FROM posts WHERE posts.type = 'Reshare'; SELECT posts.guid FROM posts WHERE posts.public = 1;

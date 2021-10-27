-- additional dependencies, one per line
-- q1; q2;
-- --> q1 \subseteq q2

SELECT users.id FROM users; SELECT owner_id FROM people;

-- reshare_constraints: (assert (forall (posts tuple t) (=> (and (t in posts) (= t.type C_RESHARE)) (and (= t.public 1) (exists (posts tuple tr) (and (tr in posts) (= t.root_guid tr.guid) (= tr.public 1)))))))
-- In our current implementation, we must write `posts.public <> 1` instead of `posts.public = 0` because we model
-- a Boolean field as an integer and don't constrain its value to be {0, 1}.
SELECT posts.id FROM posts WHERE posts.type = 'Reshare' AND posts.public <> true; SELECT posts.id FROM posts WHERE FALSE;
SELECT posts.root_guid FROM posts WHERE posts.type = 'Reshare'; SELECT posts.guid FROM posts WHERE posts.public = true;

-- contact-aspect
SELECT contacts.id FROM contacts, aspects, aspect_memberships WHERE aspect_memberships.aspect_id = aspects.id AND aspect_memberships.contact_id = contacts.id AND contacts.user_id <> aspects.user_id; SELECT contacts.id FROM contacts WHERE FALSE;

-- If I receive a notification on a post, I must be able to view the post.
SELECT notifications.recipient_id, notifications.target_id FROM notifications WHERE notifications.target_type = 'Post'; (SELECT users.id, posts.id FROM users, posts WHERE posts.`public` = true) UNION (SELECT people.owner_id, posts.id FROM people, posts WHERE posts.author_id = people.id) UNION (SELECT share_visibilities.user_id, posts.id FROM share_visibilities, posts WHERE share_visibilities.shareable_id = posts.id AND share_visibilities.shareable_type = 'Post');


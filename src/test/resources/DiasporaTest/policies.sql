-- policies must be one per line, comments must start at start of line
-- * policies not supported
-- my_info
SELECT users.* FROM users WHERE users.id = _MY_UID;
SELECT profiles.* FROM profiles, people WHERE profiles.person_id = people.id AND people.owner_id = _MY_UID;
-- visible_posts
SELECT posts.* FROM posts WHERE posts.`public` = true;
SELECT posts.* FROM posts, people WHERE posts.author_id = people.id AND people.owner_id = _MY_UID;
SELECT posts.* FROM posts, share_visibilities WHERE share_visibilities.shareable_id = posts.id AND share_visibilities.shareable_type = 'Post' AND share_visibilities.user_id = _MY_UID;
-- visible_comments
SELECT comments.* FROM comments, posts WHERE comments.commentable_type = 'Post' AND comments.commentable_id = posts.id AND posts.`public` = true;
SELECT comments.* FROM comments, posts, people WHERE comments.commentable_type = 'Post' AND comments.commentable_id = posts.id AND posts.author_id = people.id AND people.owner_id = _MY_UID;
SELECT comments.* FROM comments, posts, share_visibilities  WHERE comments.commentable_type = 'Post' AND comments.commentable_id = posts.id AND share_visibilities.shareable_id = posts.id AND share_visibilities.shareable_type = 'Post' AND share_visibilities.user_id = _MY_UID;
-- visible_mentions
SELECT mentions.* FROM mentions, posts WHERE mentions.mentions_container_type = 'Post' AND mentions.mentions_container_id = posts.id AND posts.`public` = true;
SELECT mentions.* FROM mentions, posts, people WHERE mentions.mentions_container_type = 'Post' AND mentions.mentions_container_id = posts.id AND posts.author_id = people.id AND people.owner_id = _MY_UID;
SELECT mentions.* FROM mentions, posts, share_visibilities WHERE mentions.mentions_container_type = 'Post' AND mentions.mentions_container_id = posts.id AND share_visibilities.shareable_id = posts.id AND share_visibilities.shareable_type = 'Post' AND share_visibilities.user_id = _MY_UID;
SELECT mentions.* FROM mentions, comments, posts WHERE mentions.mentions_container_type = 'Comment' AND mentions.mentions_container_id = comments.id AND comments.commentable_type = 'Post' AND comments.commentable_id = posts.id AND posts.`public` = true;
SELECT mentions.* FROM mentions, comments, posts, people WHERE mentions.mentions_container_type = 'Comment' AND mentions.mentions_container_id = comments.id AND comments.commentable_type = 'Post' AND comments.commentable_id = posts.id AND posts.author_id = people.id AND people.owner_id = _MY_UID;
SELECT mentions.* FROM mentions, comments, posts, share_visibilities  WHERE mentions.mentions_container_type = 'Comment' AND mentions.mentions_container_id = comments.id AND comments.commentable_type = 'Post' AND comments.commentable_id = posts.id AND share_visibilities.shareable_id = posts.id AND share_visibilities.shareable_type = 'Post' AND share_visibilities.user_id = _MY_UID;

-- all_people
SELECT people.* FROM people;

-- basic_profiles
SELECT profiles.id, profiles.diaspora_handle, profiles.first_name, profiles.last_name, profiles.image_url, profiles.image_url_small, profiles.image_url_medium, profiles.created_at, profiles.updated_at, profiles.full_name, profiles.nsfw, profiles.public_details, profiles.searchable, profiles.person_id FROM profiles;

-- extended_profiles
SELECT profiles.* FROM profiles WHERE profiles.public_details = true;
SELECT profiles.* FROM profiles, contacts WHERE contacts.user_id = _MY_UID AND contacts.person_id = profiles.person_id AND contacts.sharing = true;

-- visible_photos
SELECT photos.* FROM photos, people WHERE photos.author_id = people.id AND photos.pending = false AND people.owner_id = _MY_UID;
SELECT photos.* FROM photos WHERE photos.public = true AND photos.pending = false;
SELECT photos.* FROM photos, share_visibilities WHERE share_visibilities.shareable_id = photos.id AND share_visibilities.shareable_type = 'Photo' AND share_visibilities.user_id = _MY_UID AND photos.pending = false;
SELECT photos.* FROM photos, posts WHERE photos.status_message_guid = posts.guid AND posts.`public` = true;
SELECT photos.* FROM photos, posts, people WHERE photos.status_message_guid = posts.guid AND posts.author_id = people.id AND people.owner_id = _MY_UID;
SELECT photos.* FROM photos, posts, share_visibilities WHERE photos.status_message_guid = posts.guid AND share_visibilities.shareable_id = posts.id AND share_visibilities.shareable_type = 'Post' AND share_visibilities.user_id = _MY_UID;

-- visible_locations
SELECT locations.* FROM locations, posts WHERE locations.status_message_id = posts.id AND posts.`public` = true;
SELECT locations.* FROM locations, posts, people WHERE locations.status_message_id = posts.id AND posts.author_id = people.id AND people.owner_id = _MY_UID;
SELECT locations.* FROM locations, posts, share_visibilities WHERE locations.status_message_id = posts.id AND share_visibilities.shareable_id = posts.id AND share_visibilities.shareable_type = 'Post' AND share_visibilities.user_id = _MY_UID;

-- visible_polls
SELECT polls.* FROM polls, posts WHERE polls.status_message_id = posts.id AND posts.`public` = true;
SELECT polls.* FROM polls, posts, people WHERE polls.status_message_id = posts.id AND posts.author_id = people.id AND people.owner_id = _MY_UID;
SELECT polls.* FROM polls, posts, share_visibilities WHERE polls.status_message_id = posts.id AND share_visibilities.shareable_id = posts.id AND share_visibilities.shareable_type = 'Post' AND share_visibilities.user_id = _MY_UID;

-- visible_poll_answers
SELECT poll_answers.* FROM poll_answers, polls, posts WHERE poll_answers.poll_id = polls.id AND polls.status_message_id = posts.id AND posts.`public` = true;
SELECT poll_answers.* FROM poll_answers, polls, posts, people WHERE poll_answers.poll_id = polls.id AND polls.status_message_id = posts.id AND posts.author_id = people.id AND people.owner_id = _MY_UID;
SELECT poll_answers.* FROM poll_answers, polls, posts, share_visibilities WHERE poll_answers.poll_id = polls.id AND polls.status_message_id = posts.id AND share_visibilities.shareable_id = posts.id AND share_visibilities.shareable_type = 'Post' AND share_visibilities.user_id = _MY_UID;

-- visible_poll_participations
SELECT poll_participations.* FROM poll_participations, polls, posts WHERE poll_participations.poll_id = polls.id AND polls.status_message_id = posts.id AND posts.`public` = true;
SELECT poll_participations.* FROM poll_participations, polls, posts, people WHERE poll_participations.poll_id = polls.id AND polls.status_message_id = posts.id AND posts.author_id = people.id AND people.owner_id = _MY_UID;
SELECT poll_participations.* FROM poll_participations, polls, posts, share_visibilities WHERE poll_participations.poll_id = polls.id AND polls.status_message_id = posts.id AND share_visibilities.shareable_id = posts.id AND share_visibilities.shareable_type = 'Post' AND share_visibilities.user_id = _MY_UID;

-- visible_participations
SELECT participations.* FROM participations, people WHERE participations.author_id = people.id AND people.owner_id = _MY_UID;

-- visible_likes
SELECT likes.* FROM likes, posts WHERE likes.target_id = posts.id AND likes.target_type = 'Post' AND posts.`public` = true;
SELECT likes.* FROM likes, posts, people WHERE likes.target_id = posts.id AND likes.target_type = 'Post' AND posts.author_id = people.id AND people.owner_id = _MY_UID;
SELECT likes.* FROM likes, posts, share_visibilities WHERE likes.target_id = posts.id AND likes.target_type = 'Post' AND share_visibilities.shareable_id = posts.id AND share_visibilities.shareable_type = 'Post' AND share_visibilities.user_id = _MY_UID;

-- visible_taggings
SELECT taggings.* FROM tags, taggings WHERE tags.id = taggings.tag_id AND taggings.taggable_type = 'Profile';
SELECT taggings.* FROM tags, taggings, posts WHERE tags.id = taggings.tag_id AND taggings.taggable_id = posts.id AND taggings.taggable_type = 'Post' AND posts.`public` = true;
SELECT taggings.* FROM tags, taggings, posts, people WHERE tags.id = taggings.tag_id AND taggings.taggable_id = posts.id AND taggings.taggable_type = 'Post' AND posts.author_id = people.id AND people.owner_id = _MY_UID;
SELECT taggings.* FROM tags, taggings, posts, share_visibilities WHERE tags.id = taggings.tag_id AND taggings.taggable_id = posts.id AND taggings.taggable_type = 'Post' AND share_visibilities.shareable_id = posts.id AND share_visibilities.shareable_type = 'Post' AND share_visibilities.user_id = _MY_UID;

-- visible_tags
SELECT tags.* FROM tags, taggings WHERE tags.id = taggings.tag_id AND taggings.taggable_type = 'Profile';
SELECT tags.* FROM tags, taggings, posts WHERE tags.id = taggings.tag_id AND taggings.taggable_id = posts.id AND taggings.taggable_type = 'Post' AND posts.`public` = true;
SELECT tags.* FROM tags, taggings, posts, people WHERE tags.id = taggings.tag_id AND taggings.taggable_id = posts.id AND taggings.taggable_type = 'Post' AND posts.author_id = people.id AND people.owner_id = _MY_UID;
SELECT tags.* FROM tags, taggings, posts, share_visibilities WHERE tags.id = taggings.tag_id AND taggings.taggable_id = posts.id AND taggings.taggable_type = 'Post' AND share_visibilities.shareable_id = posts.id AND share_visibilities.shareable_type = 'Post' AND share_visibilities.user_id = _MY_UID;

-- visible_notifications
SELECT notifications.* FROM notifications WHERE notifications.recipient_id = _MY_UID;

-- visible_notification_actors
SELECT notification_actors.* FROM notifications, notification_actors WHERE notifications.recipient_id = _MY_UID AND notification_actors.notification_id = notifications.id;

-- visible_conv
SELECT conversations.* FROM conversations, people WHERE conversations.author_id = people.id AND people.owner_id = _MY_UID;
SELECT o_cv.*, conversations.* FROM conversation_visibilities o_cv, conversation_visibilities my_cv, conversations, people WHERE o_cv.conversation_id = my_cv.conversation_id AND conversations.id = my_cv.conversation_id AND my_cv.person_id = people.id AND people.owner_id = _MY_UID;

-- visible_messages
SELECT messages.* FROM messages, conversations, people WHERE messages.conversation_id = conversations.id AND conversations.author_id = people.id AND people.owner_id = _MY_UID;
SELECT messages.* FROM messages, conversation_visibilities, people WHERE messages.conversation_id = conversation_visibilities.conversation_id AND conversation_visibilities.person_id = people.id AND people.owner_id = _MY_UID;

-- visible_roles
SELECT roles.* FROM roles, people WHERE roles.person_id = people.id AND people.owner_id = _MY_UID;

-- visible_aspect_memberships
SELECT aspect_memberships.* FROM aspect_memberships, aspects WHERE aspects.user_id = _MY_UID AND aspect_memberships.aspect_id = aspects.id;

-- visible_mine
SELECT aspects.* FROM aspects WHERE aspects.user_id = _MY_UID;
SELECT blocks.* FROM blocks WHERE blocks.user_id = _MY_UID;
SELECT services.* FROM services WHERE services.user_id = _MY_UID;
SELECT contacts.* FROM contacts WHERE contacts.user_id = _MY_UID;
SELECT user_preferences.* FROM user_preferences WHERE user_preferences.user_id = _MY_UID;
SELECT tag_followings.* FROM tag_followings WHERE tag_followings.user_id = _MY_UID;
SELECT invitation_codes.* FROM invitation_codes WHERE invitation_codes.user_id = _MY_UID;

-- visible_aspect_visibilities
SELECT aspect_visibilities.* FROM aspect_visibilities, aspects WHERE aspect_visibilities.aspect_id = aspects.id AND aspects.user_id = _MY_UID;

-- visible_o_embed_caches
SELECT o_embed_caches.* FROM o_embed_caches, posts WHERE o_embed_caches.id = posts.o_embed_cache_id AND posts.`public` = true;
SELECT o_embed_caches.* FROM o_embed_caches, posts, people WHERE o_embed_caches.id = posts.o_embed_cache_id AND posts.author_id = people.id AND people.owner_id = _MY_UID;
SELECT o_embed_caches.* FROM o_embed_caches, posts, share_visibilities WHERE o_embed_caches.id = posts.o_embed_cache_id AND share_visibilities.shareable_id = posts.id AND share_visibilities.shareable_type = 'Post' AND share_visibilities.user_id = _MY_UID;

-- visible_open_graph_caches;
SELECT open_graph_caches.* FROM open_graph_caches, posts WHERE open_graph_caches.id = posts.open_graph_cache_id AND posts.`public` = true;
SELECT open_graph_caches.* FROM open_graph_caches, posts, people WHERE open_graph_caches.id = posts.open_graph_cache_id AND posts.author_id = people.id AND people.owner_id = _MY_UID;
SELECT open_graph_caches.* FROM open_graph_caches, posts, share_visibilities WHERE open_graph_caches.id = posts.open_graph_cache_id AND share_visibilities.shareable_id = posts.id AND share_visibilities.shareable_type = 'Post' AND share_visibilities.user_id = _MY_UID;

-- visible_by_admin
SELECT users.* FROM users, roles, people WHERE roles.person_id = people.id AND roles.name = 'admin' AND people.owner_id = _MY_UID;
SELECT o.* FROM people o, roles, people me WHERE roles.person_id = me.id AND roles.name = 'admin' AND me.owner_id = _MY_UID;
SELECT posts.* FROM posts, roles, people WHERE roles.person_id = people.id AND roles.name = 'admin' AND people.owner_id = _MY_UID;
SELECT share_visibilities.* FROM share_visibilities, roles, people WHERE roles.person_id = people.id AND roles.name = 'admin' AND people.owner_id = _MY_UID;
SELECT mentions.* FROM mentions, roles, people WHERE roles.person_id = people.id AND roles.name = 'admin' AND people.owner_id = _MY_UID;
SELECT comments.* FROM comments, roles, people WHERE roles.person_id = people.id AND roles.name = 'admin' AND people.owner_id = _MY_UID;
SELECT profiles.* FROM profiles, roles, people WHERE roles.person_id = people.id AND roles.name = 'admin' AND people.owner_id = _MY_UID;
SELECT photos.* FROM photos, roles, people WHERE roles.person_id = people.id AND roles.name = 'admin' AND people.owner_id = _MY_UID;
SELECT locations.* FROM locations, roles, people WHERE roles.person_id = people.id AND roles.name = 'admin' AND people.owner_id = _MY_UID;
SELECT polls.* FROM polls, roles, people WHERE roles.person_id = people.id AND roles.name = 'admin' AND people.owner_id = _MY_UID;
SELECT poll_participations.* FROM poll_participations, roles, people WHERE roles.person_id = people.id AND roles.name = 'admin' AND people.owner_id = _MY_UID;
SELECT poll_answers.* FROM poll_answers, roles, people WHERE roles.person_id = people.id AND roles.name = 'admin' AND people.owner_id = _MY_UID;
SELECT participations.* FROM participations, roles, people WHERE roles.person_id = people.id AND roles.name = 'admin' AND people.owner_id = _MY_UID;
SELECT likes.* FROM likes, roles, people WHERE roles.person_id = people.id AND roles.name = 'admin' AND people.owner_id = _MY_UID;
SELECT tags.* FROM tags, roles, people WHERE roles.person_id = people.id AND roles.name = 'admin' AND people.owner_id = _MY_UID;
SELECT taggings.* FROM taggings, roles, people WHERE roles.person_id = people.id AND roles.name = 'admin' AND people.owner_id = _MY_UID;
SELECT notifications.* FROM notifications, roles, people WHERE roles.person_id = people.id AND roles.name = 'admin' AND people.owner_id = _MY_UID;
SELECT notification_actors.* FROM notification_actors, roles, people WHERE roles.person_id = people.id AND roles.name = 'admin' AND people.owner_id = _MY_UID;
SELECT conversations.* FROM conversations, roles, people WHERE roles.person_id = people.id AND roles.name = 'admin' AND people.owner_id = _MY_UID;
SELECT conversation_visibilities.* FROM conversation_visibilities, roles, people WHERE roles.person_id = people.id AND roles.name = 'admin' AND people.owner_id = _MY_UID;
SELECT o.* FROM roles o, roles my_role, people WHERE my_role.person_id = people.id AND my_role.name = 'admin' AND people.owner_id = _MY_UID;
SELECT aspects.* FROM aspects, roles, people WHERE roles.person_id = people.id AND roles.name = 'admin' AND people.owner_id = _MY_UID;
SELECT aspect_memberships.* FROM aspect_memberships, roles, people WHERE roles.person_id = people.id AND roles.name = 'admin' AND people.owner_id = _MY_UID;
SELECT services.* FROM services, roles, people WHERE roles.person_id = people.id AND roles.name = 'admin' AND people.owner_id = _MY_UID;
SELECT contacts.* FROM contacts, roles, people WHERE roles.person_id = people.id AND roles.name = 'admin' AND people.owner_id = _MY_UID;
SELECT user_preferences.* FROM user_preferences, roles, people WHERE roles.person_id = people.id AND roles.name = 'admin' AND people.owner_id = _MY_UID;
SELECT tag_followings.* FROM tag_followings, roles, people WHERE roles.person_id = people.id AND roles.name = 'admin' AND people.owner_id = _MY_UID;
SELECT reports.* FROM reports, roles, people WHERE roles.person_id = people.id AND roles.name = 'admin' AND people.owner_id = _MY_UID;
SELECT blocks.* FROM blocks, roles, people WHERE roles.person_id = people.id AND roles.name = 'admin' AND people.owner_id = _MY_UID;
SELECT invitation_codes.* FROM invitation_codes, roles, people WHERE roles.person_id = people.id AND roles.name = 'admin' AND people.owner_id = _MY_UID;
SELECT messages.* FROM messages, roles, people WHERE roles.person_id = people.id AND roles.name = 'admin' AND people.owner_id = _MY_UID;
SELECT aspect_visibilities.* FROM aspect_visibilities, roles, people WHERE roles.person_id = people.id AND roles.name = 'admin' AND people.owner_id = _MY_UID;
SELECT account_deletions.* FROM account_deletions, roles, people WHERE roles.person_id = people.id AND roles.name = 'admin' AND people.owner_id = _MY_UID;
SELECT o_embed_caches.* FROM o_embed_caches, roles, people WHERE roles.person_id = people.id AND roles.name = 'admin' AND people.owner_id = _MY_UID;
SELECT open_graph_caches.* FROM open_graph_caches, roles, people WHERE roles.person_id = people.id AND roles.name = 'admin' AND people.owner_id = _MY_UID;

-- visible_by_moderators
SELECT reports.id, reports.item_id, reports.item_type, reports.reviewed, reports.text, reports.created_at, reports.updated_at, reports.user_id, users.username FROM reports, users, roles, people WHERE reports.user_id = users.id AND roles.person_id = people.id AND roles.name = 'moderator' AND people.owner_id = _MY_UID;
SELECT posts.* FROM reports, posts, roles, people WHERE reports.item_id = posts.id AND reports.item_type = 'Post' AND roles.person_id = people.id AND roles.name = 'moderator' AND people.owner_id = _MY_UID;
SELECT mentions.* FROM mentions, reports, posts, roles, people WHERE mentions.mentions_container_id = posts.id AND mentions.mentions_container_type = 'Post' AND reports.item_id = posts.id AND reports.item_type = 'Post' AND roles.person_id = people.id AND roles.name = 'moderator' AND people.owner_id = _MY_UID;
SELECT comments.* FROM reports, comments, roles, people WHERE reports.item_id = comments.id AND reports.item_type = 'Comment' AND roles.person_id = people.id AND roles.name = 'moderator' AND people.owner_id = _MY_UID;
SELECT mentions.* FROM mentions, reports, comments, roles, people WHERE mentions.mentions_container_id = comments.id AND mentions.mentions_container_type = 'Comment' AND reports.item_id = comments.id AND reports.item_type = 'Comment' AND roles.person_id = people.id AND roles.name = 'moderator' AND people.owner_id = _MY_UID;
SELECT posts.* FROM posts, reports, comments, roles, people WHERE comments.commentable_type = 'Post' AND comments.commentable_id = posts.id AND reports.item_id = comments.id AND reports.item_type = 'Comment' AND roles.person_id = people.id AND roles.name = 'moderator' AND people.owner_id = _MY_UID;


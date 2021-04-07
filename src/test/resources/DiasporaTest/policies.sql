-- policies must be one per line, comments must start at start of line
-- * policies not supported
-- my_info
SELECT users.* FROM users WHERE users.id = _MY_UID;
SELECT people.* FROM people WHERE people.owner_id = _MY_UID;
SELECT profiles.* FROM profiles, people WHERE profiles.person_id = people.id AND people.owner_id = _MY_UID;
-- visible_posts
SELECT posts.* FROM posts WHERE posts."public" <> FALSE;
SELECT posts.* FROM posts, people WHERE posts.author_id = people.id AND people.owner_id = _MY_UID;
SELECT posts.* FROM posts, share_visibilities WHERE share_visibilities.shareable_id = posts.id AND share_visibilities.shareable_type = 'Post' AND share_visibilities.user_id = _MY_UID;
-- visible_comments
SELECT comments.* FROM comments, posts WHERE comments.commentable_type = 'Post' AND comments.commentable_id = posts.id AND posts."public" <> FALSE;
SELECT comments.* FROM comments, posts, people WHERE comments.commentable_type = 'Post' AND comments.commentable_id = posts.id AND posts.author_id = people.id AND people.owner_id = _MY_UID;
SELECT comments.* FROM comments, posts, share_visibilities  WHERE comments.commentable_type = 'Post' AND comments.commentable_id = posts.id AND share_visibilities.shareable_id = posts.id AND share_visibilities.shareable_type = 'Post' AND share_visibilities.user_id = _MY_UID;
-- visible_mentions
SELECT mentions.* FROM mentions, posts WHERE mentions.mentions_container_type = 'Post' AND mentions.mentions_container_id = posts.id AND posts."public" <> FALSE;
SELECT mentions.* FROM mentions, posts, people WHERE mentions.mentions_container_type = 'Post' AND mentions.mentions_container_id = posts.id AND posts.author_id = people.id AND people.owner_id = _MY_UID;
SELECT mentions.* FROM mentions, posts, share_visibilities WHERE mentions.mentions_container_type = 'Post' AND mentions.mentions_container_id = posts.id AND share_visibilities.shareable_id = posts.id AND share_visibilities.shareable_type = 'Post' AND share_visibilities.user_id = _MY_UID;
SELECT mentions.* FROM mentions, comments, posts WHERE mentions.mentions_container_type = 'Comment' AND mentions.mentions_container_id = comments.id AND comments.commentable_type = 'Post' AND comments.commentable_id = posts.id AND posts."public" <> FALSE;
SELECT mentions.* FROM mentions, comments, posts, people WHERE mentions.mentions_container_type = 'Comment' AND mentions.mentions_container_id = comments.id AND comments.commentable_type = 'Post' AND comments.commentable_id = posts.id AND posts.author_id = people.id AND people.owner_id = _MY_UID;
SELECT mentions.* FROM mentions, comments, posts, share_visibilities  WHERE mentions.mentions_container_type = 'Comment' AND mentions.mentions_container_id = comments.id AND comments.commentable_type = 'Post' AND comments.commentable_id = posts.id AND share_visibilities.shareable_id = posts.id AND share_visibilities.shareable_type = 'Post' AND share_visibilities.user_id = _MY_UID;

-- all_people
-- isn't this a strict superset of my_info[1]?
SELECT people.* FROM people;

-- basic_profiles
SELECT profiles.* FROM profiles;

-- extended_profiles
SELECT profiles.id, profiles.bio, profiles.location, profiles.gender, profiles.birthday FROM profiles;

-- visible_photos
SELECT photos.* FROM photos, people WHERE photos.author_id = people.id AND photos.pending = FALSE AND people.owner_id = _MY_UID;
SELECT photos.* FROM photos WHERE photos.public <> FALSE AND photos.pending = FALSE;
SELECT photos.* FROM photos, share_visibilities WHERE share_visibilities.shareable_id = photos.id AND share_visibilities.shareable_type = 'Photo' AND share_visibilities.user_id = _MY_UID AND photos.pending = FALSE;
SELECT photos.* FROM photos, posts WHERE photos.status_message_guid = posts.guid AND posts."public" <> FALSE;
SELECT photos.* FROM photos, posts, people WHERE photos.status_message_guid = posts.guid AND posts.author_id = people.id AND people.owner_id = _MY_UID;
SELECT photos.* FROM photos, posts, share_visibilities WHERE photos.status_message_guid = posts.guid AND share_visibilities.shareable_id = posts.id AND share_visibilities.shareable_type = 'Post' AND share_visibilities.user_id = _MY_UID;

-- visible_locations
SELECT locations.* FROM locations, posts WHERE locations.status_message_id = posts.id AND posts."public" <> FALSE;
SELECT locations.* FROM locations, posts, people WHERE locations.status_message_id = posts.id AND posts.author_id = people.id AND people.owner_id = _MY_UID;
SELECT locations.* FROM locations, posts, share_visibilities WHERE locations.status_message_id = posts.id AND share_visibilities.shareable_id = posts.id AND share_visibilities.shareable_type = 'Post' AND share_visibilities.user_id = _MY_UID;

-- visible_polls
SELECT polls.* FROM polls, posts WHERE polls.status_message_id = posts.id AND posts."public" <> FALSE;
SELECT polls.* FROM polls, posts, people WHERE polls.status_message_id = posts.id AND posts.author_id = people.id AND people.owner_id = _MY_UID;
SELECT polls.* FROM polls, posts, share_visibilities WHERE polls.status_message_id = posts.id AND share_visibilities.shareable_id = posts.id AND share_visibilities.shareable_type = 'Post' AND share_visibilities.user_id = _MY_UID;

-- visible_participations
SELECT participations.* FROM participations, people WHERE participations.author_id = people.id AND people.owner_id = _MY_UID;

-- visible_likes
SELECT likes.* FROM likes, posts WHERE likes.target_id = posts.id AND likes.target_type = 'Post' AND posts."public" <> FALSE;
SELECT likes.* FROM likes, posts, people WHERE likes.target_id = posts.id AND likes.target_type = 'Post' AND posts.author_id = people.id AND people.owner_id = _MY_UID;
SELECT likes.* FROM likes, posts, share_visibilities WHERE likes.target_id = posts.id AND likes.target_type = 'Post' AND share_visibilities.shareable_id = posts.id AND share_visibilities.shareable_type = 'Post' AND share_visibilities.user_id = _MY_UID;

-- visible_tags
SELECT tags.*, taggings.* FROM tags, taggings, posts WHERE tags.id = taggings.tag_id AND taggings.taggable_id = posts.id AND taggings.taggable_type = 'Post' AND posts."public" <> FALSE;
SELECT tags.*, taggings.* FROM tags, taggings, posts, people WHERE tags.id = taggings.tag_id AND taggings.taggable_id = posts.id AND taggings.taggable_type = 'Post' AND posts.author_id = people.id AND people.owner_id = _MY_UID;
SELECT tags.*, taggings.* FROM tags, taggings, posts, share_visibilities WHERE tags.id = taggings.tag_id AND taggings.taggable_id = posts.id AND taggings.taggable_type = 'Post' AND share_visibilities.shareable_id = posts.id AND share_visibilities.shareable_type = 'Post' AND share_visibilities.user_id = _MY_UID;

-- visible_notificatoins
SELECT notifications.* FROM notifications WHERE notifications.recipient_id = _MY_UID;

-- visible_conv
SELECT conversations.* FROM conversations, people WHERE conversations.author_id = people.id AND people.owner_id = _MY_UID;
SELECT conversation_visibilities.* FROM conversation_visibilities, people WHERE conversation_visibilities.person_id = people.id AND people.owner_id = _MY_UID;

-- visible_roles
SELECT roles.* FROM roles, people WHERE roles.person_id = people.id AND people.id = _MY_UID;

-- visible_mine
SELECT aspects.* FROM aspects WHERE aspects.user_id = _MY_UID;
SELECT services.* FROM services WHERE services.user_id = _MY_UID;
SELECT contacts.* FROM contacts WHERE contacts.user_id = _MY_UID;
SELECT user_preferences.* FROM user_preferences WHERE user_preferences.user_id = _MY_UID;
SELECT tag_followings.* FROM tag_followings WHERE tag_followings.user_id = _MY_UID;

-- visible_by_admin
SELECT users.* FROM users, roles, people WHERE roles.person_id = people.id AND roles.name = 'admin';
-- todo: self-join
-- SELECT people.* FROM people, roles, people WHERE roles.person_id = people.id AND roles.name = 'admin';
SELECT posts.* FROM posts, roles, people WHERE roles.person_id = people.id AND roles.name = 'admin';
SELECT share_visibilities.id, share_visibilities.shareable_id, share_visibilities.hidden, share_visibilities.shareable_type, share_visibilities.user_id FROM share_visibilities, roles, people WHERE roles.person_id = people.id AND roles.name = 'admin';
SELECT mentions.* FROM mentions, roles, people WHERE roles.person_id = people.id AND roles.name = 'admin';
SELECT comments.* FROM comments, roles, people WHERE roles.person_id = people.id AND roles.name = 'admin';
SELECT profiles.* FROM profiles, roles, people WHERE roles.person_id = people.id AND roles.name = 'admin';
SELECT photos.id, photos.author_id, photos."public", photos.guid, photos.pending, photos.text, photos.remote_photo_path, photos.remote_photo_name, photos.random_string, photos.processed_image, photos.created_at, photos.updated_at, photos.unprocessed_image, photos.status_message_guid, photos.height, photos.width FROM photos, roles, people WHERE roles.person_id = people.id AND roles.name = 'admin';
SELECT locations.* FROM locations, roles, people WHERE roles.person_id = people.id AND roles.name = 'admin';
SELECT polls.* FROM polls, roles, people WHERE roles.person_id = people.id AND roles.name = 'admin';
SELECT participations.* FROM participations, roles, people WHERE roles.person_id = people.id AND roles.name = 'admin';
SELECT likes.* FROM likes, roles, people WHERE roles.person_id = people.id AND roles.name = 'admin';
SELECT tags.id, tags.name, tags.taggings_count FROM tags, roles, people WHERE roles.person_id = people.id AND roles.name = 'admin';
SELECT taggings.id, taggings.tag_id, taggings.taggable_id, taggings.taggable_type, taggings.tagger_id, taggings.tagger_type, taggings.context, taggings.created_at FROM taggings, roles, people WHERE roles.person_id = people.id AND roles.name = 'admin';
SELECT notifications.* FROM notifications, roles, people WHERE roles.person_id = people.id AND roles.name = 'admin';
SELECT conversations.* FROM conversations, roles, people WHERE roles.person_id = people.id AND roles.name = 'admin';
SELECT conversation_visibilities.* FROM conversation_visibilities, roles, people WHERE roles.person_id = people.id AND roles.name = 'admin';
-- todo: self-join
-- SELECT roles.* FROM roles, roles, people WHERE roles.person_id = people.id AND roles.name = 'admin';
SELECT aspects.* FROM aspects, roles, people WHERE roles.person_id = people.id AND roles.name = 'admin';
SELECT services.* FROM services, roles, people WHERE roles.person_id = people.id AND roles.name = 'admin';
SELECT contacts.* FROM contacts, roles, people WHERE roles.person_id = people.id AND roles.name = 'admin';
SELECT user_preferences.* FROM user_preferences, roles, people WHERE roles.person_id = people.id AND roles.name = 'admin';
SELECT tag_followings.* FROM tag_followings, roles, people WHERE roles.person_id = people.id AND roles.name = 'admin';
SELECT reports.* FROM reports, roles, people WHERE roles.person_id = people.id AND roles.name = 'admin';

-- visible_by_moderators
SELECT reports.id, reports.item_id, reports.item_type, reports.reviewed, reports.text, reports.created_at, reports.updated_at, reports.user_id, users.username FROM reports, users, roles, people WHERE reports.user_id = users.id AND roles.person_id = people.id AND roles.name = 'moderator';
SELECT posts.* FROM reports, posts, roles, people WHERE reports.item_id = posts.id AND reports.item_type = 'Post' AND roles.person_id = people.id AND roles.name = 'moderator';
SELECT mentions.* FROM mentions, reports, posts, roles, people WHERE mentions.mentions_container_id = posts.id AND mentions.mentions_container_type = 'Post' AND reports.item_id = posts.id AND reports.item_type = 'Post' AND roles.person_id = people.id AND roles.name = 'moderator';
SELECT comments.* FROM reports, comments, roles, people WHERE reports.item_id = comments.id AND reports.item_type = 'Comment' AND roles.person_id = people.id AND roles.name = 'moderator';
SELECT mentions.* FROM mentions, reports, comments, roles, people WHERE mentions.mentions_container_id = comments.id AND mentions.mentions_container_type = 'Comment' AND reports.item_id = comments.id AND reports.item_type = 'Comment' AND roles.person_id = people.id AND roles.name = 'moderator';
SELECT posts.* FROM posts, reports, comments, roles, people WHERE comments.commentable_type = 'Post' AND comments.commentable_id = posts.id AND reports.item_id = comments.id AND reports.item_type = 'Comment' AND roles.person_id = people.id AND roles.name = 'moderator';

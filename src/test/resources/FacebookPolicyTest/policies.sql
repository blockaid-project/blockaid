-- policies must be one per line, comments must start at start of line
-- * policies not supported
-- BASE_PERMISSION
SELECT uid, name, sex, can_message, can_post, allowed_restrictions, first_name, has_timeline, install_type, interests, is_app_user, is_blocked, is_minor, last_name, middle_name, name_format FROM users WHERE uid = _MY_UID;
SELECT uid2 FROM friends WHERE uid1 = _MY_UID;
-- PERMISSIONS
-- user_about_me
SELECT about_me FROM users WHERE uid = _MY_UID;
-- friend_about_me
SELECT users.about_me FROM users, friends WHERE friends.uid1 = _MY_UID AND friends.uid2 = users.uid;
-- user_likes
SELECT movies, music, books FROM users WHERE uid = _MY_UID;
-- friend_likes
SELECT users.movies, users.music, users.books FROM users, friends WHERE friends.uid1 = _MY_UID AND friends.uid2 = users.uid;
-- user_activities
SELECT activities FROM users WHERE uid = _MY_UID;
-- friend_activities
SELECT users.activities FROM users, friends WHERE friends.uid1 = _MY_UID AND friends.uid2 = users.uid;
-- user_birthday
SELECT birthday, birthday_date FROM users WHERE uid = _MY_UID;
-- friend_birthday
SELECT users.birthday, users.birthday_date FROM users, friends WHERE friends.uid1 = _MY_UID AND friends.uid2 = users.uid;
-- user_email
SELECT contact_email FROM users WHERE uid = _MY_UID;
-- Current user's, friends' uploaded photos and photos they're tagged in.
-- user_photos
SELECT pid, src, owner, modified FROM photos WHERE owner = _MY_UID;
SELECT subject, created, pid, xcoord, ycoord FROM photo_tags WHERE subject = _MY_UID;
SELECT photos.pid, photos.src, photos.owner, photos.modified, photo_tags.subject, photo_tags.created, photo_tags.pid, photo_tags.xcoord, photo_tags.ycoord FROM photos, photo_tags WHERE photos.pid = photo_tags.pid AND photo_tags.subject = _MY_UID;
-- friend_photos
SELECT photos.pid, photos.src, photos.owner, photos.modified FROM photos, friends WHERE friends.uid1 = _MY_UID AND photos.owner = friends.uid2;
SELECT photo_tags.subject, photo_tags.created, photo_tags.pid, photo_tags.xcoord, photo_tags.ycoord FROM photo_tags, friends WHERE friends.uid1 = _MY_UID AND photo_tags.subject = friends.uid2;
SELECT photos.pid, photos.src, photos.owner, photos.modified FROM photos, photo_tags, friends WHERE friends.uid1 = _MY_UID AND photo_tags.subject = friends.uid2 AND photos.pid = photo_tags.pid;
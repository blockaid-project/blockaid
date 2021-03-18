SELECT uid, about_me, activities, allowed_restrictions, name, sex, books, music, movies, birthday_date, birthday, contact_email, can_message, can_post, first_name, has_timeline, install_type, interests, is_app_user, is_blocked, is_minor, last_name, middle_name, name_format FROM users;
SELECT uid1, uid2 FROM friends;
SELECT pid, src, owner, modified FROM photos;
SELECT subject, pid, created, ycoord, xcoord FROM photo_tags;
SELECT users.* FROM users WHERE users.id = _MY_UID;

SELECT course_user_data.* FROM course_user_data WHERE course_user_data.user_id = _MY_UID;

-- Autolab reveals the distinction between a class being nonexistent (404) and
-- a user not being enrolled in an class that does exist
-- ("User john_doe@example.com is not in this course").  Strictly speaking, the
-- `id` column doesn't have to be revealed, but it doesn't contain any sensitive
-- information (`id` and `name` are a one-to-one correspondence) so we leave it in.
SELECT courses.id, courses.name FROM courses;
-- An enrolled student can see whether the course is disabled or not...
SELECT courses.id, courses.disabled FROM courses, course_user_data WHERE courses.id = course_user_data.course_id AND course_user_data.user_id = _MY_UID;
-- and can access the course if it's not disabled.
SELECT courses.* FROM courses, course_user_data WHERE courses.id = course_user_data.course_id AND course_user_data.user_id = _MY_UID AND courses.disabled = 0;
-- An instructor can view anything about the course.
SELECT courses.* FROM courses, course_user_data WHERE courses.id = course_user_data.course_id AND course_user_data.user_id = _MY_UID AND course_user_data.instructor = 1;

SELECT announcements.* FROM announcements WHERE announcements.`system` = 1;
SELECT announcements.* FROM announcements, courses, course_user_data WHERE courses.id = course_user_data.course_id AND courses.id = announcements.course_id AND course_user_data.user_id = _MY_UID AND courses.disabled = 0 AND announcements.start_date < _NOW AND announcements.end_date > _NOW;
SELECT announcements.* FROM announcements, courses, course_user_data WHERE courses.id = course_user_data.course_id AND courses.id = announcements.course_id AND course_user_data.user_id = _MY_UID AND course_user_data.instructor = 1;

-- These fields are visible whether or not the assessment is released.
SELECT assessments.id, assessments.course_id, assessments.name, assessments.start_at, assessments.category_name FROM assessments, courses, course_user_data WHERE courses.id = course_user_data.course_id AND courses.id = assessments.course_id AND course_user_data.user_id = _MY_UID and courses.disabled = 0;
SELECT assessments.* FROM assessments, courses, course_user_data WHERE courses.id = course_user_data.course_id AND courses.id = assessments.course_id AND course_user_data.user_id = _MY_UID AND assessments.start_at < _NOW AND courses.disabled = 0;

-- We allow viewing assessment user data regardless of whether the assessment is released or not
-- because it doesn't include sensitive information about the course.
SELECT assessment_user_data.* FROM assessment_user_data, course_user_data WHERE assessment_user_data.course_user_datum_id = course_user_data.id AND course_user_data.user_id = _MY_UID;

-- invisible assessment?
SELECT attachments.* FROM attachments, courses, course_user_data WHERE attachments.released = 1 AND courses.id = course_user_data.course_id AND courses.id = attachments.course_id AND course_user_data.user_id = _MY_UID;

SELECT submissions.* FROM submissions, course_user_data WHERE submissions.course_user_datum_id = course_user_data.id AND course_user_data.user_id = _MY_UID;

SELECT scores.* FROM scores, submissions, course_user_data WHERE scores.submission_id = submissions.id AND scores.released = 1 AND submissions.course_user_datum_id = course_user_data.id AND course_user_data.user_id = _MY_UID;

-- doesn't seem to include sensitive information.
SELECT score_adjustments.* FROM score_adjustments;

-- TODO: administrator has access to everything.
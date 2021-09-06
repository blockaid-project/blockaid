SELECT users.* FROM users WHERE users.id = _MY_UID;

SELECT course_user_data.* FROM course_user_data WHERE course_user_data.user_id = _MY_UID;

-- Autolab reveals the distinction between a class being nonexistent (404) and
-- a user not being enrolled in an class that does exist
-- ("User john_doe@example.com is not in this course").  Strictly speaking, the
-- `id` column doesn't have to be revealed, but it doesn't contain any sensitive
-- information (`id` and `name` are a one-to-one correspondence) so we leave it in.
SELECT courses.id, courses.name FROM courses;
-- An enrolled student can see whether the course's display name and semester (shown on front page), start and end dates (not sensitive), and whether it is disabled or not...
SELECT courses.id, courses.display_name, courses.disabled, courses.start_date, courses.end_date, courses.semester FROM courses, course_user_data WHERE courses.id = course_user_data.course_id AND course_user_data.user_id = _MY_UID;
-- and can access the course if it's not disabled.
SELECT courses.* FROM courses, course_user_data WHERE courses.id = course_user_data.course_id AND course_user_data.user_id = _MY_UID AND courses.disabled = 0;
-- An instructor can view anything about the course.
SELECT courses.* FROM courses, course_user_data WHERE courses.id = course_user_data.course_id AND course_user_data.user_id = _MY_UID AND course_user_data.instructor = 1;

SELECT announcements.* FROM announcements WHERE announcements.`system` = 1;
-- TODO(zhangwen): Autolab has two issues surrounding announcements:
--    1. Persistent announcements seem to be displayed regardless of the start & end date times.
--    2. On the announcement view frontend I can't pick the start & end date times properly.
--  Thus, these policies here allow access to announcements regardless of start & end times.
-- SELECT announcements.* FROM announcements, courses, course_user_data WHERE courses.id = course_user_data.course_id AND courses.id = announcements.course_id AND course_user_data.user_id = _MY_UID AND courses.disabled = 0 AND announcements.start_date < _NOW AND announcements.end_date > _NOW;
SELECT announcements.* FROM announcements, courses, course_user_data WHERE courses.id = course_user_data.course_id AND courses.id = announcements.course_id AND course_user_data.user_id = _MY_UID AND courses.disabled = 0;
SELECT announcements.* FROM announcements, courses, course_user_data WHERE courses.id = course_user_data.course_id AND courses.id = announcements.course_id AND course_user_data.user_id = _MY_UID AND course_user_data.instructor = 1;

-- These fields are visible whether or not the assessment is released, and whether or not the course is disabled---
-- * A list of assessments for disabled courses show up on the front page.
-- * The date-related fields are used for grace-day calculation, which involves all assignments.
SELECT assessments.id, assessments.course_id, assessments.name, assessments.display_name, assessments.start_at, assessments.end_at, assessments.due_at, assessments.max_grace_days, assessments.category_name FROM assessments, courses, course_user_data WHERE courses.id = course_user_data.course_id AND courses.id = assessments.course_id AND course_user_data.user_id = _MY_UID;
-- But other fields are only visible for released assignments, i.e., those with `start_at < _NOW`.
SELECT assessments.* FROM assessments, courses, course_user_data WHERE courses.id = course_user_data.course_id AND courses.id = assessments.course_id AND course_user_data.user_id = _MY_UID AND assessments.start_at < _NOW AND courses.disabled = 0;

-- We allow viewing assessment user data regardless of whether the assessment is released or not
-- because it doesn't include sensitive information about the course.
SELECT assessment_user_data.* FROM assessment_user_data, course_user_data WHERE assessment_user_data.course_user_datum_id = course_user_data.id AND course_user_data.user_id = _MY_UID;

-- TODO(zhangwen): The application seems fine with showing unreleased attachments.  I filed an issue on GitHub.
-- TODO(zhangwen): The application also seems fine with showing attachments of assessments that haven't started...
-- SELECT attachments.* FROM attachments, courses, course_user_data WHERE attachments.released = 1 AND courses.id = course_user_data.course_id AND courses.id = attachments.course_id AND course_user_data.user_id = _MY_UID AND courses.disabled = 0;
SELECT attachments.* FROM attachments, courses, course_user_data WHERE courses.id = course_user_data.course_id AND courses.id = attachments.course_id AND course_user_data.user_id = _MY_UID AND courses.disabled = 0;

-- Within an accessible course, Autolab allows the user to distinguish between a nonexistent submission ID vs an
-- existing one that the user has no access to.
SELECT submissions.id FROM submissions, assessments, courses, course_user_data WHERE courses.id = course_user_data.course_id AND courses.id = assessments.course_id AND course_user_data.user_id = _MY_UID AND assessments.start_at < _NOW AND courses.disabled = 0 AND submissions.assessment_id = assessments.id;
-- TODO(zhangwen): exam in progress?
SELECT submissions.* FROM submissions, course_user_data WHERE submissions.course_user_datum_id = course_user_data.id AND course_user_data.user_id = _MY_UID;

SELECT scores.* FROM scores, submissions, course_user_data WHERE scores.submission_id = submissions.id AND scores.released = 1 AND submissions.course_user_datum_id = course_user_data.id AND course_user_data.user_id = _MY_UID;

SELECT extensions.* FROM extensions, course_user_data WHERE extensions.course_user_datum_id = course_user_data.id AND course_user_data.user_id = _MY_UID;

SELECT scoreboards.* FROM scoreboards, assessments, courses, course_user_data WHERE courses.id = course_user_data.course_id AND courses.id = assessments.course_id AND course_user_data.user_id = _MY_UID AND assessments.start_at < _NOW AND courses.disabled = 0 AND scoreboards.assessment_id = assessments.id;

SELECT problems.* FROM problems, assessments, courses, course_user_data WHERE courses.id = course_user_data.course_id AND courses.id = assessments.course_id AND course_user_data.user_id = _MY_UID AND assessments.start_at < _NOW AND courses.disabled = 0 AND problems.assessment_id = assessments.id;

-- doesn't seem to include sensitive information.
SELECT score_adjustments.* FROM score_adjustments;

-- From `app/controllers/schedulers_controller.rb`:
--   Tasks don't actually get accurately scheduled, but with each request, we check all schedulers, and if one hasn't
--   ran in more than its period's time, it's function is run.
-- Thus, every page load checks for _any_ tasks ready to run; this necessitates a policy that allows reading rows from
-- the `scheduler` table irrespective of `course_id`.  This is unideal, but can't be rectified without extensive
-- application change.
SELECT scheduler.* FROM scheduler;

SELECT schema_migrations.* FROM schema_migrations;

-- TODO: administrator has access to everything.